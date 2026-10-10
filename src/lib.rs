//! Deterministic, exact-rational SMT solving in pure Rust.
//!
//! `rz3` is a small DPLL(T)/CDCL solver focused on reproducible, embeddable
//! reasoning without native dependencies. Arithmetic in the linear-arithmetic
//! core uses arbitrary-precision rationals (`num-rational`/`num-bigint`) and
//! symbolic strict bounds instead of floating-point approximations.
//!
//! The project is intentionally narrower than mature solvers such as Z3. The
//! LRA/LIA path is the most developed part of the crate, while arrays, EUF,
//! bit-vectors, strings, floating-point, quantifiers, non-linear arithmetic and
//! the SMT-LIB front-end are implemented as focused subsets. Some unresolved
//! cases return [`SolverResult::Unknown`]; callers should handle that result
//! explicitly.
//!
//! # Example
//!
//! ```
//! use rz3::ast::{Expr, Type};
//! use rz3::{Rz3Solver, SolverResult};
//!
//! let mut solver = Rz3Solver::new();
//! let x = || Expr::Var("x".to_string(), Type::Int);
//!
//! solver.assert(&Expr::Gt(Box::new(x()), Box::new(Expr::Int(0))));
//! solver.assert(&Expr::Lt(Box::new(x()), Box::new(Expr::Int(0))));
//!
//! assert_eq!(solver.check(), SolverResult::Unsat);
//! ```
//!
pub mod ast;
pub mod bvring;
pub mod driver;
pub mod eval;
pub mod parser;
pub mod proof;
pub mod sat;
pub mod tactic;
pub mod theory;

use crate::ast::{Expr, ModelValue, Type};
use crate::bvring::BvRing;
use crate::sat::CdclSolver;
use crate::tactic::{Simplifier, SolveEqs, TacticEngine};
use crate::theory::array_reduce::ArrayReducer;
use crate::theory::cc::Cc;
use crate::theory::diff::DiffLogic;
use crate::theory::fp::FpSolver;
use crate::theory::linarith::LinArith;
use crate::theory::skolem::Skolemizer;
use crate::theory::{
    ArraySolver, EufSolver, NlaSolver, QuantifierSolver, StringSolver, TheorySolver,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeMap;

/// The online theories (linear arithmetic and congruence closure) seen as one hook.
struct Hooks<'a> {
    lin: &'a mut LinArith,
    cc: &'a mut Cc,
    dl: &'a mut DiffLogic,
}

impl crate::sat::TheoryHook for Hooks<'_> {
    fn new_level(&mut self) {
        self.lin.new_level();
        self.cc.new_level();
        self.dl.new_level();
    }

    fn backtrack(&mut self, level: usize) {
        self.lin.backtrack(level);
        self.cc.backtrack(level);
        self.dl.backtrack(level);
    }

    fn assign(&mut self, lit: i32) -> Result<(), Vec<i32>> {
        self.lin.assign(lit)?;
        self.cc.assign(lit)?;
        self.dl.assign(lit)
    }

    #[allow(clippy::type_complexity)]
    fn check(&mut self) -> Result<Vec<(i32, Vec<i32>)>, Vec<i32>> {
        let mut implied = self.lin.check()?;
        implied.extend(self.cc.check()?);
        implied.extend(self.dl.check()?);
        Ok(implied)
    }
}

/// `r` rounded to a multiple of `2^-bits` (integers stay as they are).
fn grid_point(r: &BigRational, bits: u32) -> BigRational {
    if r.is_integer() {
        return r.clone();
    }
    let scale = BigRational::from_integer(num_bigint::BigInt::from(1) << bits);
    (r * &scale).round() / scale
}

fn var_name(e: &Expr) -> String {
    match e {
        Expr::Var(n, _) => n.clone(),
        _ => String::new(),
    }
}

/// Outcome of the generic (array / string / fp / quantifier / nonlinear / equality) theories.
enum OtherTheories {
    Consistent,
    Unknown,
    /// A conflict clause (or blocking clause) was added; search again.
    Refuted,
    Unsat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}

/// Phase counters, for profiling and for reporting how a run spent its time.
/// Printed by the CLI when `RZ3_STATS` is set. Times are wall-clock nanoseconds.
#[derive(Debug, Default, Clone)]
pub struct Stats {
    pub assert_ns: u128,
    pub sat_ns: u128,
    pub theory_ns: u128,
    pub certify_ns: u128,
    pub lin_ns: u128,
    pub dl_ns: u128,
    pub dl_repair_ns: u128,
    pub dl_search_ns: u128,
    pub dl_propagations: u64,
    pub propagations: u64,
    pub check_calls: u64,
    pub dpll_iterations: u64,
    pub theory_conflicts: u64,
    pub branches: u64,
    pub pivots: u64,
    pub array_instances: u64,
    pub nonlinear_lemmas: u64,
    pub sat: crate::sat::SatStats,
    /// Why the last `check()` answered `Unknown`, if it did.
    pub unknown_reason: Option<&'static str>,
    pub atoms: usize,
    pub sat_vars: i32,
}

pub struct Rz3Solver {
    stats: Stats,
    /// Optional wall-clock deadline: `check()` answers `Unknown` once it passes.
    deadline: Option<std::time::Instant>,
    sat_solver: CdclSolver,
    expr_to_lit: BTreeMap<Expr, i32>,
    lit_to_expr: BTreeMap<i32, Expr>,
    bv_vars: BTreeMap<(String, usize), i32>,
    bv_expr_to_bits: BTreeMap<Expr, Vec<i32>>,
    next_sat_var: i32,
    symbol_table: BTreeMap<String, Type>,
    tactic_engine: TacticEngine,

    lin: LinArith,
    cc: Cc,
    diff: DiffLogic,
    arrays: ArrayReducer,
    skolem: Skolemizer,
    /// Normalised (NNF, skolemised) formulas that still contain a universal quantifier.
    quant_formulas: Vec<Expr>,
    /// Instance lemmas already produced, to avoid repeating them.
    quant_done: std::collections::BTreeSet<Expr>,
    /// Variables standing for nonlinear factors / partial products (memoised).
    nl_vars: BTreeMap<Expr, Expr>,
    /// Monomials whose sign lemmas have been added.
    nl_sign_done: std::collections::BTreeSet<String>,
    /// Nonlinear lemma instances already asserted.
    nl_done: std::collections::BTreeSet<Expr>,
    /// While set, assertions bypass skolemisation (instance lemmas refer to the quantifier atom).
    skip_skolem: bool,
    /// Comparison atoms with nonlinear content (decided or declined by the NLA theory).
    nla_atoms: Vec<(Expr, i32)>,
    /// Array / string / floating-point / quantifier content is present, so the generic
    /// per-atom theories must be fed on every iteration.
    slow: bool,
    euf: EufSolver,
    array: ArraySolver,
    quant: QuantifierSolver,
    string: StringSolver,
    nla: NlaSolver,
    fp: FpSolver,
    proof_gen: crate::proof::Proof,

    /// All asserted expressions in order — used for push/pop rebuild.
    assertion_history: Vec<Expr>,
    /// Stack of assertion_history lengths at each push() call.
    scope_stack: Vec<usize>,
    /// Set when an asserted formula contains something no theory interprets (for
    /// example a bit-vector operator the bit-blaster does not encode, or an
    /// application of an undeclared function). A satisfiable verdict is then not
    /// trustworthy, so `check()` answers `Unknown` instead of `Sat`.
    incomplete: bool,
    /// Ackermann reduction: application (with already-reduced arguments) -> fresh variable.
    app_vars: BTreeMap<Expr, Expr>,
    /// Per function symbol, the applications seen so far (for pairwise congruence lemmas).
    app_by_fn: BTreeMap<String, Vec<(Vec<Expr>, Expr)>>,
    /// Fresh variables standing for `div`/`to_int` terms (memoised by the reduced term).
    def_vars: BTreeMap<Expr, Expr>,
    /// Division-like terms whose divisor may be zero: (kind, dividend, divisor, value variable).
    zero_div_terms: Vec<(u8, Expr, Expr, Expr)>,
    /// Too many such terms to relate pairwise: a model with a zero divisor is then not trusted.
    zero_div_overflow: bool,
    /// Fresh variables standing for term-level `ite` (memoised by the reduced term).
    ite_vars: BTreeMap<Expr, Expr>,
    /// Every formula handed to the theories (after `ite` lifting, Ackermann reduction and
    /// simplification). A satisfiable verdict is certified by evaluating all of them.
    processed: Vec<Expr>,
}

impl Default for Rz3Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Rz3Solver {
    pub fn new() -> Self {
        let mut tactic_engine = TacticEngine::new();
        tactic_engine.add_tactic(Box::new(BvRing));
        tactic_engine.add_tactic(Box::new(Simplifier));
        tactic_engine.add_tactic(Box::new(SolveEqs));
        Self {
            sat_solver: CdclSolver::new(),
            expr_to_lit: BTreeMap::new(),
            lit_to_expr: BTreeMap::new(),
            bv_vars: BTreeMap::new(),
            bv_expr_to_bits: BTreeMap::new(),
            next_sat_var: 1,
            symbol_table: BTreeMap::new(),
            tactic_engine,
            lin: LinArith::new(),
            cc: Cc::new(),
            diff: DiffLogic::new(),
            arrays: ArrayReducer::new(),
            skolem: Skolemizer::new(),
            quant_formulas: Vec::new(),
            quant_done: std::collections::BTreeSet::new(),
            nl_vars: BTreeMap::new(),
            nl_sign_done: std::collections::BTreeSet::new(),
            nl_done: std::collections::BTreeSet::new(),
            skip_skolem: false,
            nla_atoms: Vec::new(),
            slow: false,
            euf: EufSolver::new(),
            array: ArraySolver::new(),
            quant: QuantifierSolver::new(),
            string: StringSolver::new(),
            nla: NlaSolver::new(),
            fp: FpSolver::new(),
            proof_gen: crate::proof::Proof::new(),
            assertion_history: Vec::new(),
            scope_stack: Vec::new(),
            stats: Stats::default(),
            deadline: None,
            incomplete: false,
            app_vars: BTreeMap::new(),
            app_by_fn: BTreeMap::new(),
            def_vars: BTreeMap::new(),
            zero_div_terms: Vec::new(),
            zero_div_overflow: false,
            ite_vars: BTreeMap::new(),
            processed: Vec::new(),
        }
    }

    /// Make `check()` give up (answering `Unknown`) after `limit` of wall-clock time.
    pub fn set_time_limit(&mut self, limit: std::time::Duration) {
        self.deadline = Some(std::time::Instant::now() + limit);
    }

    /// Phase counters accumulated so far.
    pub fn stats(&self) -> Stats {
        if std::env::var_os("RZ3_ATOMS").is_some() {
            let mut hist: BTreeMap<String, usize> = BTreeMap::new();
            for e in self.expr_to_lit.keys() {
                let name = format!("{e:?}");
                let head: String = name.chars().take_while(|c| c.is_alphanumeric()).collect();
                *hist.entry(head).or_default() += 1;
            }
            eprintln!("atoms by kind: {hist:?}");
            eprintln!(
                "arrays (sel_vars, sources, deferred, indices): {:?}",
                self.arrays.sizes()
            );
        }
        let mut st = self.stats.clone();
        st.atoms = self.expr_to_lit.len();
        st.sat_vars = self.next_sat_var;
        st
    }

    /// Save current assertion context. Paired with pop().
    pub fn push(&mut self) {
        self.scope_stack.push(self.assertion_history.len());
    }

    /// Restore to the assertion context at the last push().
    /// Uses rebuild-from-history (correct but O(n) per pop).
    pub fn pop(&mut self) {
        if let Some(saved_len) = self.scope_stack.pop() {
            self.assertion_history.truncate(saved_len);
            self.rebuild();
        }
    }

    fn rebuild(&mut self) {
        let history = std::mem::take(&mut self.assertion_history);
        let scopes = std::mem::take(&mut self.scope_stack);
        let sym = std::mem::take(&mut self.symbol_table);

        self.sat_solver = CdclSolver::new();
        self.expr_to_lit = BTreeMap::new();
        self.lit_to_expr = BTreeMap::new();
        self.bv_vars = BTreeMap::new();
        self.bv_expr_to_bits = BTreeMap::new();
        self.next_sat_var = 1;
        let mut te = TacticEngine::new();
        te.add_tactic(Box::new(BvRing));
        te.add_tactic(Box::new(Simplifier));
        te.add_tactic(Box::new(SolveEqs));
        self.tactic_engine = te;
        self.lin = LinArith::new();
        self.cc = Cc::new();
        self.diff = DiffLogic::new();
        self.arrays = ArrayReducer::new();
        self.skolem = Skolemizer::new();
        self.quant_formulas = Vec::new();
        self.quant_done = std::collections::BTreeSet::new();
        self.nl_vars = BTreeMap::new();
        self.nl_sign_done = std::collections::BTreeSet::new();
        self.nl_done = std::collections::BTreeSet::new();
        self.nla_atoms = Vec::new();
        self.slow = false;
        self.euf = EufSolver::new();
        self.array = ArraySolver::new();
        self.quant = QuantifierSolver::new();
        self.string = StringSolver::new();
        self.nla = NlaSolver::new();
        self.fp = FpSolver::new();
        self.proof_gen = crate::proof::Proof::new();
        self.incomplete = false;
        self.app_vars = BTreeMap::new();
        self.app_by_fn = BTreeMap::new();
        self.def_vars = BTreeMap::new();
        self.zero_div_terms = Vec::new();
        self.zero_div_overflow = false;
        self.ite_vars = BTreeMap::new();
        self.processed = Vec::new();

        self.symbol_table = sym;
        self.assertion_history = history;
        self.scope_stack = scopes;

        for expr in self.assertion_history.clone() {
            self.assert_no_track(&expr);
        }
    }

    fn assert_no_track(&mut self, expr: &Expr) {
        let started = std::time::Instant::now();
        self.assert_no_track_inner(expr);
        self.stats.assert_ns += started.elapsed().as_nanos();
    }

    fn assert_no_track_inner(&mut self, expr: &Expr) {
        {
            // New atoms are registered with the theories: they must be at the root first.
            let mut hooks = Hooks {
                lin: &mut self.lin,
                cc: &mut self.cc,
                dl: &mut self.diff,
            };
            self.sat_solver.unwind(&mut hooks);
        }
        let typed = self.resolve_expr_types(expr);
        // Quantifiers: negation normal form, existentials replaced by skolem symbols. An
        // opaque `exists` atom would make `exists x. false` satisfiable.
        let typed = if !self.skip_skolem && Skolemizer::contains_quantifier(&typed) {
            let (nnf, symbols) = self.skolem.run(&typed);
            for (name, ty) in symbols {
                self.declare_fun(name, ty);
            }
            if nnf.any_subterm(&|e| matches!(e, Expr::ForAll(_, _))) {
                // Instances can refute a model but never prove one: no `sat` from here on.
                self.incomplete = true;
                self.quant_formulas.push(nnf.clone());
            }
            nnf
        } else {
            typed
        };
        let mut def_lemmas = Vec::new();
        let typed = self.eliminate_defs(&typed, &mut def_lemmas);
        for lemma in def_lemmas {
            self.assert_no_track(&lemma);
        }
        let mut ite_lemmas = Vec::new();
        let typed = self.eliminate_ite(&typed, &mut ite_lemmas);
        for lemma in ite_lemmas {
            self.assert_no_track(&lemma);
        }
        let mut nl_lemmas = Vec::new();
        let typed = self.purify_nonlinear(&typed, &mut nl_lemmas);
        for lemma in nl_lemmas {
            self.assert_no_track(&lemma);
        }
        let typed = self.lift_ite(&typed);
        let mut array_lemmas = Vec::new();
        let typed = self.arrays.reduce(&typed, &mut array_lemmas);
        for lemma in array_lemmas {
            self.assert_no_track(&lemma);
        }
        if self.arrays.truncated {
            self.incomplete = true;
        }
        let mut lemmas = Vec::new();
        let typed = self.ackermannize(&typed, &mut lemmas);
        for lemma in lemmas {
            self.assert_no_track(&lemma);
        }
        self.scan_support(&typed);
        let simplified = self.tactic_engine.apply(typed);
        if let Expr::Bool(true) = simplified {
            return;
        }
        if let Expr::Bool(false) = simplified {
            self.sat_solver.ok = false;
            return;
        }
        self.processed.push(simplified.clone());
        if Self::needs_generic_theories(&simplified) {
            self.slow = true;
        }
        self.euf.assert(&simplified);
        self.array.assert(&simplified);
        self.quant.assert(&simplified);
        self.string.assert(&simplified);
        self.nla.assert(&simplified);
        self.fp.assert(&simplified);
        let lit = self.tseitin(&simplified);
        let _ = self.sat_solver.add_clause(vec![lit]);
    }

    /// Share `ite` instead of duplicating the formula around it.
    ///
    /// A term-level `ite(c, t, e)` becomes a fresh variable `v` of the same sort together with
    /// `(c -> v = t) /\ (!c -> v = e)`; a Boolean `ite` becomes `(c /\ t) \/ (!c /\ e)`.
    /// Splitting every atom that contains an `ite` (the old `lift_ite`) doubles the formula
    /// per `ite` and exploded on array-heavy inputs (23k atoms from a few hundred bytes).
    /// `lift_ite` stays as the fallback for an `ite` whose sort cannot be determined.
    fn eliminate_ite(&mut self, expr: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if matches!(expr, Expr::ForAll(_, _) | Expr::Exists(_, _)) {
            return expr.clone();
        }
        let rebuilt = expr.map_children(&mut |c| self.eliminate_ite(c, lemmas));
        let Expr::Ite(c, t, e) = &rebuilt else {
            return rebuilt;
        };
        let ty = match (self.infer_type(t), self.infer_type(e)) {
            (Some(Type::Real), Some(Type::Int | Type::Real))
            | (Some(Type::Int), Some(Type::Real)) => Some(Type::Real),
            (Some(a), _) => Some(a),
            (None, b) => b,
        };
        match ty {
            Some(Type::Bool) => Expr::Or(vec![
                Expr::And(vec![(**c).clone(), (**t).clone()]),
                Expr::And(vec![Expr::Not(c.clone()), (**e).clone()]),
            ]),
            Some(ty) if ty != Type::Unknown => {
                if let Some(v) = self.ite_vars.get(&rebuilt) {
                    return v.clone();
                }
                let v = Expr::Var(format!("__ite_{}", self.ite_vars.len()), ty);
                lemmas.push(Expr::And(vec![
                    Expr::Or(vec![
                        Expr::Not(c.clone()),
                        Expr::Eq(Box::new(v.clone()), t.clone()),
                    ]),
                    Expr::Or(vec![
                        (**c).clone(),
                        Expr::Eq(Box::new(v.clone()), e.clone()),
                    ]),
                ]));
                self.ite_vars.insert(rebuilt.clone(), v.clone());
                v
            }
            _ => rebuilt,
        }
    }

    /// Replace every `ite` by plain boolean structure so that no theory ever sees one.
    ///
    /// * boolean `ite(c, t, e)`  ->  `(c /\ t) \/ (!c /\ e)`
    /// * a term-level `ite` inside an atom is split on its condition:
    ///   `A[ite(c, t, e)]  ->  (c /\ A[t]) \/ (!c /\ A[e])`
    ///
    /// Without this the arithmetic and bit-vector encoders treated an `ite` term as an
    /// unconstrained fresh variable and reported satisfiable.
    fn lift_ite(&self, expr: &Expr) -> Expr {
        if !expr.any_subterm(&|e| matches!(e, Expr::Ite(_, _, _))) {
            return expr.clone();
        }
        match expr {
            Expr::And(_) | Expr::Or(_) | Expr::Not(_) | Expr::Implies(_, _) => {
                expr.map_children(&mut |c| self.lift_ite(c))
            }
            Expr::ForAll(_, _) | Expr::Exists(_, _) => expr.clone(),
            Expr::Eq(a, b)
                if self.infer_type(a) == Some(Type::Bool)
                    && self.infer_type(b) == Some(Type::Bool) =>
            {
                expr.map_children(&mut |c| self.lift_ite(c))
            }
            Expr::Ite(c, t, e) if self.infer_type(t) == Some(Type::Bool) => {
                let c = self.lift_ite(c);
                let t = self.lift_ite(t);
                let e = self.lift_ite(e);
                Expr::Or(vec![
                    Expr::And(vec![c.clone(), t]),
                    Expr::And(vec![Expr::Not(Box::new(c)), e]),
                ])
            }
            _ => {
                let Some(target) = Self::first_ite(expr) else {
                    return expr.clone();
                };
                let Expr::Ite(c, t, e) = &target else {
                    return expr.clone();
                };
                let with_t = Self::replace_term(expr, &target, t);
                let with_e = Self::replace_term(expr, &target, e);
                self.lift_ite(&Expr::Or(vec![
                    Expr::And(vec![(**c).clone(), with_t]),
                    Expr::And(vec![Expr::Not(c.clone()), with_e]),
                ]))
            }
        }
    }

    fn first_ite(expr: &Expr) -> Option<Expr> {
        if matches!(expr, Expr::Ite(_, _, _)) {
            return Some(expr.clone());
        }
        let mut found = None;
        expr.map_children(&mut |c| {
            if found.is_none() {
                found = Self::first_ite(c);
            }
            Expr::Bool(true)
        });
        found
    }

    fn replace_term(expr: &Expr, target: &Expr, with: &Expr) -> Expr {
        if expr == target {
            return with.clone();
        }
        expr.map_children(&mut |c| Self::replace_term(c, target, with))
    }

    /// Replace `div`, `mod`, `to_int` and `is_int` by fresh integer variables constrained
    /// by their defining inequalities (SMT-LIB Euclidean division):
    ///   `q = div x c`  <=>  `c*q <= x < c*q + |c|`   (c != 0)
    ///   `q = to_int x` <=>  `q <= x < q + 1`
    /// A divisor that may be zero leaves the quotient unconstrained there, as the standard
    /// treats `div x 0` as an uninterpreted function; satisfiable verdicts are then
    /// withheld (`incomplete`), unsat remains valid.
    fn eliminate_defs(&mut self, expr: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if matches!(expr, Expr::ForAll(_, _) | Expr::Exists(_, _)) {
            return expr.clone();
        }
        let rebuilt = expr.map_children(&mut |c| self.eliminate_defs(c, lemmas));
        match &rebuilt {
            Expr::IntDiv(x, c) => self.division_variable(x, c, lemmas),
            Expr::IntMod(x, c) => self.modulo_variable(x, c, lemmas),
            // Real division by a non-constant: q = x / y  <=>  y = 0 \/ q * y = x. The value at
            // y = 0 is unspecified in SMT-LIB, so q stays free there.
            Expr::Div(x, y) if !Self::nonzero_constant(y) => {
                let key = rebuilt.clone();
                if let Some(v) = self.def_vars.get(&key) {
                    return v.clone();
                }
                let q = Expr::Var(format!("__rdiv_{}", self.def_vars.len()), Type::Real);
                lemmas.push(Expr::Or(vec![
                    Expr::Eq(y.clone(), Box::new(Expr::Int(0))),
                    Expr::Eq(
                        Box::new(Expr::Mul(vec![q.clone(), (**y).clone()])),
                        x.clone(),
                    ),
                ]));
                self.register_zero_div(2, x, y, &q, lemmas);
                self.def_vars.insert(key, q.clone());
                q
            }
            Expr::ToInt(x) => self.floor_variable(x, lemmas),
            Expr::IsInt(x) => {
                let q = self.floor_variable(x, lemmas);
                Expr::Eq(Box::new(q), x.clone())
            }
            _ => rebuilt,
        }
    }

    fn nonzero_constant(c: &Expr) -> bool {
        c.as_constant()
            .is_some_and(|v| v != num_rational::BigRational::from_integer(0.into()))
    }

    /// SMT-LIB makes `div`, `mod` and `/` by zero total functions of the dividend: two occurrences
    /// with equal dividends and zero divisors must have the same value. Each new term whose
    /// divisor may be zero is related to the earlier ones of the same kind. The number of terms
    /// is capped; beyond it the certification refuses models with a zero divisor instead.
    fn register_zero_div(
        &mut self,
        kind: u8,
        x: &Expr,
        c: &Expr,
        v: &Expr,
        lemmas: &mut Vec<Expr>,
    ) {
        const CAP: usize = 40;
        if Self::nonzero_constant(c) {
            return;
        }
        let zero = |e: &Expr| Expr::Eq(Box::new(e.clone()), Box::new(Expr::Int(0)));
        let same_kind: Vec<(Expr, Expr, Expr)> = self
            .zero_div_terms
            .iter()
            .filter(|t| t.0 == kind)
            .map(|t| (t.1.clone(), t.2.clone(), t.3.clone()))
            .collect();
        if same_kind.len() >= CAP {
            self.zero_div_overflow = true;
            return;
        }
        for (x2, c2, v2) in same_kind {
            lemmas.push(Expr::Or(vec![
                Expr::Not(Box::new(zero(c))),
                Expr::Not(Box::new(zero(&c2))),
                Expr::Not(Box::new(Expr::Eq(Box::new(x.clone()), Box::new(x2)))),
                Expr::Eq(Box::new(v.clone()), Box::new(v2)),
            ]));
        }
        self.zero_div_terms
            .push((kind, x.clone(), c.clone(), v.clone()));
    }

    /// `mod x c` as its own variable. The identity `mod x c = x - c * div x c` only holds when
    /// `c != 0`; for a zero divisor the standard leaves the value unspecified, so rewriting it
    /// as `x - c * q` would force `mod x 0 = x` and could refute satisfiable problems.
    fn modulo_variable(&mut self, x: &Expr, c: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = Expr::IntMod(Box::new(x.clone()), Box::new(c.clone()));
        if let Some(v) = self.def_vars.get(&key) {
            return v.clone();
        }
        let q = self.division_variable(x, c, lemmas);
        let r = Expr::Var(format!("__mod_{}", self.def_vars.len()), Type::Int);
        let definition = Expr::Eq(
            Box::new(r.clone()),
            Box::new(Expr::Sub(vec![x.clone(), Expr::Mul(vec![c.clone(), q])])),
        );
        let nonzero_const = c
            .as_constant()
            .is_some_and(|v| v != num_rational::BigRational::from_integer(0.into()));
        if nonzero_const {
            lemmas.push(definition);
        } else {
            lemmas.push(Expr::Or(vec![
                Expr::Eq(Box::new(c.clone()), Box::new(Expr::Int(0))),
                definition,
            ]));
        }
        self.register_zero_div(1, x, c, &r, lemmas);
        self.def_vars.insert(key, r.clone());
        r
    }

    fn division_variable(&mut self, x: &Expr, c: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = Expr::IntDiv(Box::new(x.clone()), Box::new(c.clone()));
        if let Some(v) = self.def_vars.get(&key) {
            return v.clone();
        }
        let q = Expr::Var(format!("__div_{}", self.def_vars.len()), Type::Int);
        let cq = Expr::Mul(vec![c.clone(), q.clone()]);
        let abs_c = match c.as_constant() {
            Some(r) => {
                Expr::from_rational(&if r < num_rational::BigRational::from_integer(0.into()) {
                    -r
                } else {
                    r
                })
            }
            None => Expr::Ite(
                Box::new(Expr::Ge(Box::new(c.clone()), Box::new(Expr::Int(0)))),
                Box::new(c.clone()),
                Box::new(Expr::Sub(vec![Expr::Int(0), c.clone()])),
            ),
        };
        let bounds = Expr::And(vec![
            Expr::Le(Box::new(cq.clone()), Box::new(x.clone())),
            Expr::Lt(Box::new(x.clone()), Box::new(Expr::Add(vec![cq, abs_c]))),
        ]);
        let nonzero_const = c
            .as_constant()
            .is_some_and(|r| r != num_rational::BigRational::from_integer(0.into()));
        if nonzero_const {
            lemmas.push(bounds);
        } else {
            lemmas.push(Expr::Or(vec![
                Expr::Eq(Box::new(c.clone()), Box::new(Expr::Int(0))),
                bounds,
            ]));
        }
        self.register_zero_div(0, x, c, &q, lemmas);
        self.def_vars.insert(key, q.clone());
        q
    }

    fn floor_variable(&mut self, x: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = Expr::ToInt(Box::new(x.clone()));
        if let Some(v) = self.def_vars.get(&key) {
            return v.clone();
        }
        let q = Expr::Var(format!("__toint_{}", self.def_vars.len()), Type::Int);
        lemmas.push(Expr::And(vec![
            Expr::Le(Box::new(q.clone()), Box::new(x.clone())),
            Expr::Lt(
                Box::new(x.clone()),
                Box::new(Expr::Add(vec![q.clone(), Expr::Int(1)])),
            ),
        ]));
        self.def_vars.insert(key, q.clone());
        q
    }

    /// Ackermann reduction of declared function symbols.
    ///
    /// Each application `f(t1..tn)` becomes a fresh variable and, for every earlier
    /// application `f(s1..sn)`, the lemma `(s1 = t1 /\ ..) -> f(s) = f(t)` is added.
    /// This keeps uninterpreted functions exact when their arguments or results are
    /// arithmetic or bit-vector terms, which the equality-only congruence closure
    /// cannot relate (it treated `f(a+1)` and `f(b+1)` as unrelated even if `a = b`).
    fn ackermannize(&mut self, expr: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if matches!(expr, Expr::ForAll(_, _) | Expr::Exists(_, _)) {
            return expr.clone();
        }
        let rebuilt = expr.map_children(&mut |c| self.ackermannize(c, lemmas));
        if let Expr::App(name, args) = &rebuilt {
            if self.is_native_function(name, args.len()) {
                return rebuilt;
            }
            if let Some(Type::Fn(params, ret)) = self.symbol_table.get(name).cloned() {
                if params.len() == args.len() {
                    return self.application_variable(name, args, &ret, lemmas);
                }
            }
        }
        rebuilt
    }

    fn application_variable(
        &mut self,
        name: &str,
        args: &[Expr],
        ret: &Type,
        lemmas: &mut Vec<Expr>,
    ) -> Expr {
        let key = Expr::App(name.to_string(), args.to_vec());
        if let Some(var) = self.app_vars.get(&key) {
            return var.clone();
        }
        let var = Expr::Var(
            format!("__ack_{}_{}", name, self.app_vars.len()),
            ret.clone(),
        );
        let earlier = self.app_by_fn.get(name).cloned().unwrap_or_default();
        for (earlier_args, earlier_var) in earlier {
            let same_args: Vec<Expr> = earlier_args
                .iter()
                .zip(args)
                .map(|(p, a)| Expr::Eq(Box::new(p.clone()), Box::new(a.clone())))
                .collect();
            let premise = if same_args.len() == 1 {
                same_args[0].clone()
            } else {
                Expr::And(same_args)
            };
            lemmas.push(Expr::Or(vec![
                Expr::Not(Box::new(premise)),
                Expr::Eq(Box::new(earlier_var), Box::new(var.clone())),
            ]));
        }
        self.app_by_fn
            .entry(name.to_string())
            .or_default()
            .push((args.to_vec(), var.clone()));
        self.app_vars.insert(key, var.clone());
        var
    }

    /// Flag formulas that contain constructs no theory interprets.
    fn scan_support(&mut self, expr: &Expr) {
        let symbols = &self.symbol_table;
        let unsupported = expr.any_subterm(&|e| match e {
            Expr::App(name, args) => {
                let declared = name == "fp"
                    || name.starts_with("fp.")
                    || matches!(symbols.get(name), Some(Type::Fn(_, _)));
                // Bit-vector arguments live in the SAT core; EUF cannot relate them.
                let bv_arg = args.iter().any(|a| matches!(a.get_type(), Type::BitVec(_)));
                !declared || (bv_arg && !name.starts_with("fp"))
            }
            _ => false,
        });
        if unsupported {
            self.incomplete = true;
        }
    }

    pub fn declare_fun(&mut self, name: String, ty: Type) {
        self.symbol_table.insert(name, ty);
    }

    pub fn declare_fun_signature(&mut self, name: String, params: Vec<Type>, return_type: Type) {
        let ty = if params.is_empty() {
            return_type
        } else {
            Type::Fn(params, Box::new(return_type))
        };
        self.declare_fun(name, ty);
    }

    fn resolve_expr_types(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::Var(name, _) => {
                let ty = self
                    .symbol_table
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| expr.get_type());
                Expr::Var(name.clone(), ty)
            }
            Expr::And(args) => Expr::And(args.iter().map(|a| self.resolve_expr_types(a)).collect()),
            Expr::Or(args) => Expr::Or(args.iter().map(|a| self.resolve_expr_types(a)).collect()),
            Expr::Not(inner) => Expr::Not(Box::new(self.resolve_expr_types(inner))),
            Expr::Implies(a, b) => Expr::Implies(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Ite(c, t, e) => Expr::Ite(
                Box::new(self.resolve_expr_types(c)),
                Box::new(self.resolve_expr_types(t)),
                Box::new(self.resolve_expr_types(e)),
            ),
            Expr::Eq(a, b) => Expr::Eq(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Lt(a, b) => Expr::Lt(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Le(a, b) => Expr::Le(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Gt(a, b) => Expr::Gt(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Ge(a, b) => Expr::Ge(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Add(args) => Expr::Add(args.iter().map(|a| self.resolve_expr_types(a)).collect()),
            Expr::Sub(args) => Expr::Sub(args.iter().map(|a| self.resolve_expr_types(a)).collect()),
            Expr::Mul(args) => Expr::Mul(args.iter().map(|a| self.resolve_expr_types(a)).collect()),
            Expr::Div(a, b) => Expr::Div(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::App(name, args) => Expr::App(
                name.clone(),
                args.iter().map(|a| self.resolve_expr_types(a)).collect(),
            ),
            Expr::BvAdd(a, b) => Expr::BvAdd(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvSub(a, b) => Expr::BvSub(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvMul(a, b) => Expr::BvMul(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvAnd(a, b) => Expr::BvAnd(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvOr(a, b) => Expr::BvOr(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvXor(a, b) => Expr::BvXor(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvNot(inner) => Expr::BvNot(Box::new(self.resolve_expr_types(inner))),
            Expr::BvShl(a, b) => Expr::BvShl(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvLshr(a, b) => Expr::BvLshr(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvAshr(a, b) => Expr::BvAshr(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvUle(a, b) => Expr::BvUle(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvUlt(a, b) => Expr::BvUlt(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvSle(a, b) => Expr::BvSle(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvSlt(a, b) => Expr::BvSlt(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::BvExtract(h, l, inner) => {
                Expr::BvExtract(*h, *l, Box::new(self.resolve_expr_types(inner)))
            }
            Expr::BvConcat(a, b) => Expr::BvConcat(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            Expr::Select(a, i) => Expr::Select(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(i)),
            ),
            Expr::Store(a, i, v) => Expr::Store(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(i)),
                Box::new(self.resolve_expr_types(v)),
            ),
            Expr::ForAll(vars, body) => {
                Expr::ForAll(vars.clone(), Box::new(self.resolve_expr_types(body)))
            }
            Expr::Exists(vars, body) => {
                Expr::Exists(vars.clone(), Box::new(self.resolve_expr_types(body)))
            }
            Expr::StrConcat(args) => {
                Expr::StrConcat(args.iter().map(|a| self.resolve_expr_types(a)).collect())
            }
            Expr::StrLen(inner) => Expr::StrLen(Box::new(self.resolve_expr_types(inner))),
            Expr::StrContains(a, b) => Expr::StrContains(
                Box::new(self.resolve_expr_types(a)),
                Box::new(self.resolve_expr_types(b)),
            ),
            _ => expr.clone(),
        }
    }

    fn infer_type(&self, expr: &Expr) -> Option<Type> {
        match expr {
            Expr::Var(name, ty) => {
                if *ty != Type::Unknown {
                    Some(ty.clone())
                } else {
                    self.symbol_table.get(name).cloned()
                }
            }
            Expr::App(name, _) => match self.symbol_table.get(name) {
                Some(Type::Fn(_, ret)) => Some((**ret).clone()),
                Some(ty) => Some(ty.clone()),
                None => {
                    let ty = expr.get_type();
                    if ty == Type::Unknown {
                        None
                    } else {
                        Some(ty)
                    }
                }
            },
            _ => {
                let ty = expr.get_type();
                if ty == Type::Unknown {
                    None
                } else {
                    Some(ty)
                }
            }
        }
    }

    pub fn get_model(&self) -> BTreeMap<String, ModelValue> {
        let mut model = self.raw_model();
        // Hide the solver's own variables (`__ack_`, `__ite_`, `__sel_`, ...): only symbols
        // the user declared, or ones that are not generated, belong in a model.
        model.retain(|name, _| self.symbol_table.contains_key(name) || !name.starts_with("__"));
        // Every declared constant has a value in a model, even one no assertion mentions.
        for (name, ty) in &self.symbol_table {
            if model.contains_key(name) {
                continue;
            }
            let default = match ty {
                Type::Bool => Some(ModelValue::Bool(false)),
                Type::Int => Some(ModelValue::Int(BigInt::from(0))),
                Type::Real => Some(ModelValue::Real(BigRational::from_integer(BigInt::from(0)))),
                Type::BitVec(w) => Some(ModelValue::BitVec(num_bigint::BigUint::default(), *w)),
                _ => None,
            };
            if let Some(v) = default {
                model.insert(name.clone(), v);
            }
        }
        model
    }

    /// The model including the solver's internal variables (Ackermann application
    /// variables), which formulas handed to the theories refer to.
    fn raw_model(&self) -> BTreeMap<String, ModelValue> {
        let mut model = BTreeMap::new();

        // Bool variables from SAT assignments
        for (expr, &lit) in &self.expr_to_lit {
            if let Expr::Var(name, ty) = expr {
                let val = matches!(
                    self.sat_solver.get_lit_value(lit),
                    crate::sat::Assignment::True
                );
                let mv = match ty {
                    crate::ast::Type::Bool => ModelValue::Bool(val),
                    _ => continue,
                };
                model.insert(name.clone(), mv);
            }
        }

        // Bit-vector variables
        for ((name, bit), &lit) in &self.bv_vars {
            let val = matches!(
                self.sat_solver.get_lit_value(lit),
                crate::sat::Assignment::True
            );
            let entry = model
                .entry(name.clone())
                .or_insert(ModelValue::BitVec(num_bigint::BigUint::default(), 0));
            if let ModelValue::BitVec(curr, width) = entry {
                if val {
                    curr.set_bit(*bit as u64, true);
                }
                *width = (*width).max(bit + 1);
            }
        }

        // Real/Int variables from LRA simplex assignments
        for (name, val) in self.lin.assignments() {
            model
                .entry(name.clone())
                .or_insert_with(|| match self.symbol_table.get(&name) {
                    Some(crate::ast::Type::Int) => ModelValue::Int(val.to_integer()),
                    _ => ModelValue::Real(val),
                });
        }

        model
    }

    pub fn get_value(&self, expr: &Expr) -> Option<ModelValue> {
        let typed = self.resolve_expr_types(expr);
        if let Some(value) = Self::literal_model_value(&typed) {
            return Some(value);
        }
        if let Expr::Var(name, _) = &typed {
            return self.get_model().get(name).cloned();
        }
        let model = self.get_model();
        // Applications of declared functions need the function table built from the model.
        let raw = self.raw_model();
        let funs = self.function_table(&raw);
        // The visible model also fills in defaults for declared constants the problem never mentions.
        let mut merged = raw;
        merged.extend(model);
        if let Some(v) = crate::eval::eval_with(&typed, &merged, &funs) {
            match v {
                crate::eval::Value::Bool(b) => return Some(ModelValue::Bool(b)),
                crate::eval::Value::Num(r) => {
                    return Some(
                        if r.is_integer() && matches!(self.infer_type(&typed), Some(Type::Int)) {
                            ModelValue::Int(r.to_integer())
                        } else {
                            ModelValue::Real(r)
                        },
                    )
                }
                crate::eval::Value::Bv(v, w) => return Some(ModelValue::BitVec(v, w)),
            }
        }
        self.fp
            .get_model_value(&typed)
            .or_else(|| self.euf.get_model_value(&typed))
            .or_else(|| self.array.get_model_value(&typed))
            .or_else(|| self.string.get_model_value(&typed))
            .or_else(|| self.nla.get_model_value(&typed))
            .or_else(|| self.quant.get_model_value(&typed))
    }

    fn literal_model_value(expr: &Expr) -> Option<ModelValue> {
        match expr {
            Expr::Bool(value) => Some(ModelValue::Bool(*value)),
            Expr::Int(value) => Some(ModelValue::Int(BigInt::from(*value))),
            Expr::Real(value, scale) => {
                let denominator = BigInt::from(10u8).pow(*scale);
                Some(ModelValue::Real(BigRational::new(
                    BigInt::from(*value),
                    denominator,
                )))
            }
            Expr::BvConst(value, width) => Some(ModelValue::BitVec(value.clone(), *width)),
            _ => None,
        }
    }

    fn get_or_create_lit(&mut self, expr: &Expr) -> i32 {
        if let Some(&lit) = self.expr_to_lit.get(expr) {
            lit
        } else {
            let lit = self.next_sat_var;
            self.next_sat_var += 1;
            self.expr_to_lit.insert(expr.clone(), lit);
            self.lit_to_expr.insert(lit, expr.clone());
            if self.is_arith_atom(expr) {
                self.lin.register(lit, expr);
                if let Some(d) = self.lin.take_dl() {
                    self.diff.register(&d);
                }
                if expr.has_unhandled_nonlinear() {
                    self.nla_atoms.push((expr.clone(), lit));
                }
            } else if self.is_cc_atom(expr) {
                self.cc.register(lit, expr);
            } else if let Expr::Eq(a, _) = expr {
                // Equalities over Boolean or bit-vector terms are fully encoded in the SAT
                // core. Any other equality needs congruence closure.
                if !matches!(
                    self.infer_type(a),
                    Some(Type::Bool | Type::BitVec(_) | Type::Int | Type::Real)
                ) {
                    self.slow = true;
                }
            }
            lit
        }
    }

    /// Equality of uninterpreted-sort terms, or a predicate over such terms: both handled by
    /// the congruence-closure theory.
    fn is_cc_atom(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Eq(a, _) => matches!(self.infer_type(a), Some(Type::Sort(_))),
            Expr::App(name, args) => self.is_native_function(name, args.len()),
            _ => false,
        }
    }

    /// A declared function the congruence closure treats natively: every argument has an
    /// uninterpreted sort and the result is a sort or Boolean. (Everything else is
    /// Ackermann-reduced so arithmetic and bit-vector arguments are compared exactly.)
    fn is_native_function(&self, name: &str, arity: usize) -> bool {
        match self.symbol_table.get(name) {
            Some(Type::Fn(params, ret)) => {
                params.len() == arity
                    && !params.is_empty()
                    && params.iter().all(|p| matches!(p, Type::Sort(_)))
                    && matches!(**ret, Type::Sort(_) | Type::Bool)
            }
            _ => false,
        }
    }

    /// A comparison between numbers (as opposed to Boolean, bit-vector or sort equalities).
    fn is_arith_atom(&self, expr: &Expr) -> bool {
        let numeric = |e: &Expr| {
            matches!(self.infer_type(e), Some(Type::Int | Type::Real))
                || matches!(e, Expr::Int(_) | Expr::Real(_, _) | Expr::BigRat(_, _))
        };
        match expr {
            Expr::Le(_, _) | Expr::Lt(_, _) | Expr::Ge(_, _) | Expr::Gt(_, _) => true,
            Expr::Eq(a, b) => numeric(a) || numeric(b),
            _ => false,
        }
    }

    /// Content that only the generic per-atom theories (arrays, strings, floating point,
    /// quantifiers) understand.
    fn needs_generic_theories(expr: &Expr) -> bool {
        expr.any_subterm(&|e| match e {
            Expr::Select(_, _)
            | Expr::Store(_, _, _)
            | Expr::ForAll(_, _)
            | Expr::Exists(_, _)
            | Expr::StrConst(_)
            | Expr::StrConcat(_)
            | Expr::StrLen(_)
            | Expr::StrContains(_, _) => true,
            Expr::App(name, _) => name == "fp" || name.starts_with("fp."),
            Expr::Var(_, Type::Float(_)) => true,
            _ => false,
        })
    }

    fn is_bv(&self, expr: &Expr) -> bool {
        matches!(self.infer_type(expr), Some(Type::BitVec(_)))
            || matches!(
                expr,
                Expr::BvConst(_, _)
                    | Expr::BvAdd(_, _)
                    | Expr::BvSub(_, _)
                    | Expr::BvMul(_, _)
                    | Expr::BvAnd(_, _)
                    | Expr::BvOr(_, _)
                    | Expr::BvXor(_, _)
                    | Expr::BvNot(_)
                    | Expr::BvShl(_, _)
                    | Expr::BvLshr(_, _)
                    | Expr::BvAshr(_, _)
                    | Expr::BvExtract(_, _, _)
                    | Expr::BvConcat(_, _)
            )
    }

    pub fn assert(&mut self, expr: &Expr) {
        self.assertion_history.push(expr.clone());
        self.assert_no_track(expr);
    }

    fn tseitin(&mut self, expr: &Expr) -> i32 {
        match expr {
            Expr::ForAll(_, _) | Expr::Select(_, _) | Expr::Store(_, _, _) => {
                self.get_or_create_lit(expr)
            }
            Expr::Bool(true) => {
                let lit = self.get_or_create_lit(expr);
                self.sat_solver.add_clause(vec![lit]);
                lit
            }
            Expr::Bool(false) => {
                let lit = self.get_or_create_lit(expr);
                self.sat_solver.add_clause(vec![-lit]);
                lit
            }
            Expr::Not(inner) => {
                let lit = self.tseitin(inner);
                -lit
            }
            Expr::And(args) => {
                let res_lit = self.get_or_create_lit(expr);
                let arg_lits: Vec<i32> = args.iter().map(|arg| self.tseitin(arg)).collect();
                for &arg_lit in &arg_lits {
                    self.sat_solver.add_clause(vec![-res_lit, arg_lit]);
                }
                let mut clause = arg_lits.iter().map(|&l| -l).collect::<Vec<_>>();
                clause.push(res_lit);
                self.sat_solver.add_clause(clause);
                res_lit
            }
            Expr::Or(args) => {
                let res_lit = self.get_or_create_lit(expr);
                let arg_lits: Vec<i32> = args.iter().map(|arg| self.tseitin(arg)).collect();
                for &arg_lit in &arg_lits {
                    self.sat_solver.add_clause(vec![-arg_lit, res_lit]);
                }
                let mut clause = arg_lits;
                clause.push(-res_lit);
                self.sat_solver.add_clause(clause);
                res_lit
            }
            Expr::Implies(a, b) => {
                let not_a_or_b = Expr::Or(vec![Expr::Not(a.clone()), *b.clone()]);
                self.tseitin(&not_a_or_b)
            }
            Expr::Lt(_a, _b) | Expr::Gt(_a, _b) => self.get_or_create_lit(expr),
            Expr::BvUle(_, _) | Expr::BvUlt(_, _) | Expr::BvSle(_, _) | Expr::BvSlt(_, _) => {
                self.bv_predicate(expr)
            }
            Expr::Eq(a, b) => {
                if self.is_bv(a) || self.is_bv(b) {
                    // Encoded entirely in the SAT core; the arithmetic/EUF theories must
                    // not see (and mis-abstract) bit-vector terms.
                    self.bv_predicate(expr)
                } else if self.infer_type(a) == Some(Type::Bool) {
                    // Equivalence of two formulas is purely propositional. It must not be
                    // registered as an atom: the arithmetic/EUF theories would receive an
                    // `=` between formulas and treat the operands as opaque terms.
                    // Equalities between Boolean *terms* (variables, applications) are
                    // different: congruence closure needs to see them.
                    let term_like = |e: &Expr| matches!(e, Expr::Var(_, _) | Expr::App(_, _));
                    let res_lit = if term_like(a) && term_like(b) {
                        self.get_or_create_lit(expr)
                    } else {
                        let fresh = self.next_sat_var;
                        self.next_sat_var += 1;
                        fresh
                    };
                    let lit_a = self.tseitin(a);
                    let lit_b = self.tseitin(b);
                    self.sat_solver.add_clause(vec![lit_a, -lit_b, -res_lit]);
                    self.sat_solver.add_clause(vec![-lit_a, lit_b, -res_lit]);
                    self.sat_solver.add_clause(vec![-lit_a, -lit_b, res_lit]);
                    self.sat_solver.add_clause(vec![lit_a, lit_b, res_lit]);
                    res_lit
                } else {
                    let fresh = !self.expr_to_lit.contains_key(expr);
                    let lit = self.get_or_create_lit(expr);
                    // Trichotomy for arithmetic equalities: `a = b \/ a < b \/ a > b`.
                    // A negated equality then always carries a strict bound, so the
                    // simplex never has to repair a bare disequality (it gives up with
                    // Unknown on unbounded ones).
                    if fresh && matches!(self.infer_type(a), Some(Type::Int | Type::Real)) {
                        let lt = self.get_or_create_lit(&Expr::Lt(a.clone(), b.clone()));
                        let gt = self.get_or_create_lit(&Expr::Gt(a.clone(), b.clone()));
                        self.sat_solver.add_clause(vec![lit, lt, gt]);
                    }
                    lit
                }
            }
            _ => self.get_or_create_lit(expr),
        }
    }

    /// Function interpretation implied by the Ackermann variables of the current model.
    fn function_table(&self, model: &BTreeMap<String, ModelValue>) -> crate::eval::FunTable {
        let mut table = crate::eval::FunTable::new();
        for (name, entries) in &self.app_by_fn {
            for (args, var) in entries {
                let values: Option<Vec<_>> =
                    args.iter().map(|a| crate::eval::eval(a, model)).collect();
                if let (Some(values), Some(result)) = (values, crate::eval::eval(var, model)) {
                    table
                        .entry(name.clone())
                        .or_default()
                        .push((values, result));
                }
            }
        }
        table
    }

    /// SAT literal for a bit-vector comparison/equality. If the encoder cannot express
    /// it, a free literal is returned and the solver is flagged incomplete (no Sat).
    fn bv_predicate(&mut self, expr: &Expr) -> i32 {
        let mut blaster = crate::theory::bv::BitBlaster::new(
            &mut self.sat_solver,
            &mut self.bv_vars,
            &mut self.bv_expr_to_bits,
            &mut self.next_sat_var,
        );
        let lit = blaster.predicate(expr);
        let unsupported = blaster.unsupported;
        if unsupported {
            self.incomplete = true;
        }
        match lit {
            Some(l) => l,
            None => {
                let fresh = self.next_sat_var;
                self.next_sat_var += 1;
                fresh
            }
        }
    }

    /// Record why a verdict was declined (visible with `RZ3_STATS` / `RZ3_TRACE`).
    fn unknown(&mut self, why: &'static str) -> SolverResult {
        self.stats.unknown_reason = Some(why);
        if std::env::var_os("RZ3_TRACE").is_some() {
            eprintln!("unknown: {why}");
        }
        SolverResult::Unknown
    }

    pub fn check(&mut self) -> SolverResult {
        // Branch-and-bound lemmas added for integer variables in this call.
        const MAX_BRANCHES: usize = 5000;
        const MAX_QUANT_ROUNDS: usize = 8;
        const MAX_NL_ROUNDS: usize = 400;
        let mut nl_rounds = 0usize;
        let mut branches = 0usize;
        let mut quant_rounds = 0usize;
        self.stats.check_calls += 1;
        loop {
            if self.deadline.is_some_and(|d| std::time::Instant::now() > d) {
                return self.unknown("time limit");
            }
            self.stats.dpll_iterations += 1;
            // Propagating through the difference graph pays only when it covers the whole
            // arithmetic part of the problem; mixed problems keep just its cycle detection.
            self.diff.propagate =
                !self.diff.is_empty() && self.diff.num_atoms() == self.lin.num_atoms();
            self.diff.enabled = std::env::var_os("RZ3_DIFF_LOGIC").is_some();
            let sat_started = std::time::Instant::now();
            let status = {
                let mut hooks = Hooks {
                    lin: &mut self.lin,
                    cc: &mut self.cc,
                    dl: &mut self.diff,
                };
                self.sat_solver.solve_with(&mut hooks, self.deadline)
            };
            self.stats.sat_ns += sat_started.elapsed().as_nanos();
            self.stats.pivots = self.lin.pivots();
            self.stats.sat = self.sat_solver.stats;
            self.stats.theory_conflicts = self.lin.conflicts;
            self.stats.lin_ns = self.lin.time_ns;
            self.stats.dl_ns = self.diff.time_ns;
            self.stats.dl_repair_ns = self.diff.repair_ns;
            self.stats.dl_search_ns = self.diff.search_ns;
            self.stats.dl_propagations = self.diff.propagations;
            match status {
                crate::sat::SolveStatus::Unsat => return SolverResult::Unsat,
                crate::sat::SolveStatus::Interrupted => return self.unknown("time limit"),
                crate::sat::SolveStatus::Sat => {}
            }
            let theory_started = std::time::Instant::now();

            // ---- the other theories, only when their content is present
            match self.check_other_theories() {
                OtherTheories::Consistent => {}
                OtherTheories::Unknown => {
                    self.stats.theory_ns += theory_started.elapsed().as_nanos();
                    return self.unknown("other theories undecided (string/nonlinear)");
                }
                OtherTheories::Refuted => {
                    self.stats.theory_ns += theory_started.elapsed().as_nanos();
                    continue;
                }
                OtherTheories::Unsat => return SolverResult::Unsat,
            }
            self.stats.theory_ns += theory_started.elapsed().as_nanos();

            // The simplex works over the rationals. An `Int` variable with a fractional
            // value is not a model: split on it (branch and bound).
            if let Some((name, floor)) = self.lin.fractional_int() {
                branches += 1;
                self.stats.branches += 1;
                if branches > MAX_BRANCHES {
                    return self.unknown("integer branching budget exhausted");
                }
                let Some(low) = num_traits::ToPrimitive::to_i64(&floor.to_big().to_integer())
                else {
                    return self.unknown("integer branch bound out of range");
                };
                let Some(high) = low.checked_add(1) else {
                    return self.unknown("integer branch bound overflow");
                };
                let x = Expr::Var(name, Type::Int);
                self.assert(&Expr::Or(vec![
                    Expr::Le(Box::new(x.clone()), Box::new(Expr::Int(low))),
                    Expr::Ge(Box::new(x), Box::new(Expr::Int(high))),
                ]));
                continue;
            }

            // Incremental linearization of nonlinear products: refine until the model is exact.
            if !self.lin.monomials().is_empty() {
                let model = self.raw_model();
                // The abstract product variables may be wrong while the real variables already
                // satisfy every assertion with exact products (the certifier evaluates the
                // true products): then there is nothing to refine.
                let funs = self.function_table(&model);
                let none = crate::eval::FunTable::new();
                let satisfied =
                    !self.processed.iter().any(|f| {
                        crate::eval::holds(f, &model, &none) != crate::eval::Verdict::True
                    }) && !self.assertion_history.iter().any(|f| {
                        let typed = self.resolve_expr_types(f);
                        crate::eval::holds(&typed, &model, &funs) == crate::eval::Verdict::False
                    });
                let lemmas = if satisfied {
                    Vec::new()
                } else {
                    self.nonlinear_lemmas(&model)
                };
                if !lemmas.is_empty() {
                    nl_rounds += 1;
                    // Irrational solutions (e.g. x*x = 2) make tangent points grow without
                    // bound; give up early instead of burning time on huge rationals.
                    let oversized = self.lin.monomials().iter().any(|mono| {
                        [&mono.x, &mono.y].iter().any(|e| {
                            matches!(
                                crate::eval::eval(e, &model),
                                Some(crate::eval::Value::Num(r))
                                    if r.numer().bits() > 160 || r.denom().bits() > 160
                            )
                        })
                    });
                    if oversized {
                        return self.unknown("nonlinear model values grew too large");
                    }
                    if nl_rounds > MAX_NL_ROUNDS {
                        return self.unknown("nonlinear refinement budget exhausted");
                    }
                    self.stats.nonlinear_lemmas += lemmas.len() as u64;
                    for lemma in lemmas {
                        self.assert_no_track(&lemma);
                    }
                    continue;
                }
            }

            // Lazily instantiated array lemmas: add those the current model violates.
            if self.arrays.active() {
                let full_model = self.raw_model();
                let funs = self.function_table(&full_model);
                let violated = self.arrays.take_violated(&|lemma| match crate::eval::holds(
                    lemma,
                    &full_model,
                    &funs,
                ) {
                    crate::eval::Verdict::True => Some(true),
                    crate::eval::Verdict::False => Some(false),
                    crate::eval::Verdict::Unknown => None,
                });
                if !violated.is_empty() {
                    self.stats.array_instances += violated.len() as u64;
                    for lemma in violated {
                        self.assert(&lemma);
                    }
                    continue;
                }
            }

            // Ground-term instantiation of the remaining universal quantifiers.
            if !self.quant_formulas.is_empty() && quant_rounds < MAX_QUANT_ROUNDS {
                let instances = self.quantifier_instances();
                if !instances.is_empty() {
                    quant_rounds += 1;
                    // Consequences of the problem, not user assertions: kept out of the history.
                    if std::env::var_os("RZ3_QDEBUG").is_some() {
                        for l in &instances {
                            eprintln!("INSTANCE {l:?}");
                        }
                    }
                    self.skip_skolem = true;
                    for lemma in instances {
                        self.assert_no_track(&lemma);
                    }
                    self.skip_skolem = false;
                    continue;
                }
            }

            // The legacy quantifier solver is no longer asked for lemmas: an audit found one of
            // its instances to be invalid (a wrong `unsat`). `quantifier_instances` above
            // replaces it; the legacy array / string solvers are kept for the generic path.
            let (array_lemmas, quant_lemmas, string_lemmas): (Vec<Expr>, Vec<Expr>, Vec<Expr>) =
                if self.slow {
                    (
                        self.array.generate_lemmas(),
                        Vec::new(),
                        self.string.generate_lemmas(),
                    )
                } else {
                    (Vec::new(), Vec::new(), Vec::new())
                };
            if !(array_lemmas.is_empty() && quant_lemmas.is_empty() && string_lemmas.is_empty()) {
                for lemma in array_lemmas
                    .into_iter()
                    .chain(quant_lemmas)
                    .chain(string_lemmas)
                {
                    self.assert(&lemma);
                }
                continue;
            }
            // A live universally-quantified assertion can never be CERTIFIED sat by finite
            // E-matching/MBQI instantiation: reaching a lemma fixpoint means "no counterexample
            // among the ground terms explored", not "true for the whole domain" (RZ3-2).
            if self.slow && self.quant.is_unknown() {
                return self.unknown("quantifiers incomplete");
            }
            if self.slow && self.fp.is_unknown() {
                return self.unknown("floating-point term not evaluable");
            }
            // A term was abstracted or never interpreted: Sat is unproven.
            if self.incomplete || self.lin.abstracted {
                return self.unknown("abstracted or uninterpreted term");
            }
            // Independent certification: the extracted model must satisfy every formula the
            // theories were given and every formula the user asserted. If it does not, the
            // verdict is not reported (that would be a wrong Sat); formulas the evaluator
            // cannot interpret (arrays, strings, floating point, ...) are not judged.
            let certify_started = std::time::Instant::now();
            let full_model = self.raw_model();
            let funs = self.function_table(&full_model);
            let none = crate::eval::FunTable::new();
            // `div`/`mod`/`/` by zero are total functions of the dividend; the pairwise lemmas of
            // `register_zero_div` enforce that. Only when there were too many such terms to relate
            // is a model with a zero (or unevaluable) divisor refused.
            let zero_divisor = self.zero_div_overflow
                && self.assertion_history.iter().any(|f| {
                    self.resolve_expr_types(f).any_subterm(&|e| match e {
                        Expr::IntDiv(_, d) | Expr::IntMod(_, d) | Expr::Div(_, d) => !matches!(
                            crate::eval::eval(d, &full_model),
                            Some(crate::eval::Value::Num(r)) if !num_traits::Zero::is_zero(&r)
                        ),
                        _ => false,
                    })
                });
            if zero_divisor {
                return self.unknown("division by zero in the model");
            }
            let violated =
                self.processed.iter().any(|f| {
                    crate::eval::holds(f, &full_model, &none) == crate::eval::Verdict::False
                }) || self.assertion_history.iter().any(|f| {
                    let typed = self.resolve_expr_types(f);
                    crate::eval::holds(&typed, &full_model, &funs) == crate::eval::Verdict::False
                });
            self.stats.certify_ns += certify_started.elapsed().as_nanos();
            if violated {
                if std::env::var_os("RZ3_TRACE").is_some() {
                    for f in &self.processed {
                        if crate::eval::holds(f, &full_model, &none) == crate::eval::Verdict::False
                        {
                            eprintln!("violated (processed): {f:?}");
                        }
                    }
                    eprintln!("model: {full_model:?}");
                }
                return self.unknown("model failed certification");
            }
            return SolverResult::Sat;
        }
    }

    /// Ground terms of the problem (no bound variable), grouped by sort.
    fn ground_terms(&self) -> BTreeMap<Type, Vec<Expr>> {
        fn walk(
            e: &Expr,
            bound: &mut Vec<String>,
            out: &mut BTreeMap<Type, std::collections::BTreeSet<Expr>>,
        ) {
            match e {
                Expr::ForAll(vars, body) | Expr::Exists(vars, body) => {
                    let depth = bound.len();
                    bound.extend(vars.iter().map(|(n, _)| n.clone()));
                    walk(body, bound, out);
                    bound.truncate(depth);
                }
                _ => {
                    let ground =
                        !e.any_subterm(&|x| matches!(x, Expr::Var(n, _) if bound.contains(n)));
                    let ty = e.get_type();
                    if ground
                        && !matches!(ty, Type::Bool | Type::Unknown | Type::Fn(_, _))
                        && matches!(
                            e,
                            Expr::Var(_, _)
                                | Expr::App(_, _)
                                | Expr::Int(_)
                                | Expr::Real(_, _)
                                | Expr::BigRat(_, _)
                                | Expr::BvConst(_, _)
                                | Expr::Add(_)
                                | Expr::Sub(_)
                                | Expr::Mul(_)
                        )
                    {
                        out.entry(ty).or_default().insert(e.clone());
                    }
                    e.map_children(&mut |c| {
                        walk(c, bound, out);
                        c.clone()
                    });
                }
            }
        }
        let mut out: BTreeMap<Type, std::collections::BTreeSet<Expr>> = BTreeMap::new();
        for f in self
            .quant_formulas
            .iter()
            .chain(self.assertion_history.iter())
        {
            walk(f, &mut Vec::new(), &mut out);
        }
        // Seeds, so that bodies with only bound variables still get instantiated.
        out.entry(Type::Int).or_default().insert(Expr::Int(0));
        out.entry(Type::Real).or_default().insert(Expr::Real(0, 0));
        out.into_iter()
            .map(|(k, v)| (k, v.into_iter().take(40).collect()))
            .collect()
    }

    /// Instances `U -> body[t]` of every universal `U` still in the problem, for ground terms
    /// `t` of the right sort. Bounded per round; the caller iterates a few rounds.
    fn quantifier_instances(&mut self) -> Vec<Expr> {
        const PER_ROUND: usize = 4000;
        let terms = self.ground_terms();
        let mut universals: Vec<Expr> = Vec::new();
        fn collect(e: &Expr, out: &mut Vec<Expr>) {
            if matches!(e, Expr::ForAll(_, _)) && !out.contains(e) {
                out.push(e.clone());
            }
            e.map_children(&mut |c| {
                collect(c, out);
                c.clone()
            });
        }
        for f in self.quant_formulas.clone() {
            collect(&f, &mut universals);
        }
        let mut lemmas = Vec::new();
        for u in universals {
            let Expr::ForAll(vars, body) = &u else {
                continue;
            };
            // candidate tuples
            let mut tuples: Vec<Vec<Expr>> = vec![Vec::new()];
            for (_, ty) in vars {
                let Some(cands) = terms.get(ty) else {
                    tuples.clear();
                    break;
                };
                let mut next = Vec::new();
                for t in &tuples {
                    for c in cands {
                        if next.len() >= PER_ROUND {
                            break;
                        }
                        let mut t2 = t.clone();
                        t2.push(c.clone());
                        next.push(t2);
                    }
                }
                tuples = next;
            }
            for tuple in tuples {
                let mut inst = (**body).clone();
                for ((name, _), term) in vars.iter().zip(&tuple) {
                    inst = crate::theory::skolem::substitute(&inst, name, term);
                }
                let lemma = Expr::Or(vec![Expr::Not(Box::new(u.clone())), inst]);
                if self.quant_done.insert(lemma.clone()) {
                    lemmas.push(lemma);
                    if lemmas.len() >= PER_ROUND {
                        return lemmas;
                    }
                }
            }
        }
        lemmas
    }

    /// Make every nonlinear product a plain `x * y` of two variables (partial products and
    /// non-variable factors get a fresh variable with a defining equation), so the
    /// monomials can be refined one by one.
    fn purify_nonlinear(&mut self, expr: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if matches!(expr, Expr::ForAll(_, _) | Expr::Exists(_, _)) {
            return expr.clone();
        }
        let rebuilt = expr.map_children(&mut |c| self.purify_nonlinear(c, lemmas));
        let Expr::Mul(args) = &rebuilt else {
            return rebuilt;
        };
        let consts: Vec<Expr> = args
            .iter()
            .filter(|a| a.as_constant().is_some())
            .cloned()
            .collect();
        let others: Vec<Expr> = args
            .iter()
            .filter(|a| a.as_constant().is_none())
            .cloned()
            .collect();
        if others.len() < 2 {
            return rebuilt;
        }
        if others.len() == 2
            && consts.is_empty()
            && others.iter().all(|a| matches!(a, Expr::Var(_, _)))
        {
            return rebuilt; // already canonical
        }
        let vars: Vec<Expr> = others
            .iter()
            .map(|t| self.factor_variable(t, lemmas))
            .collect();
        let mut acc = vars[0].clone();
        for (i, v) in vars.iter().enumerate().skip(1) {
            let product = Expr::Mul(vec![acc.clone(), v.clone()]);
            acc = if i + 1 == vars.len() {
                product
            } else {
                self.factor_variable(&product, lemmas)
            };
        }
        if consts.is_empty() {
            acc
        } else {
            let mut parts = consts;
            parts.push(acc);
            Expr::Mul(parts)
        }
    }

    /// A variable equal to the term `t` (itself when it already is one).
    fn factor_variable(&mut self, t: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if let Expr::Var(_, _) = t {
            return t.clone();
        }
        if let Some(v) = self.nl_vars.get(t) {
            return v.clone();
        }
        let v = Expr::Var(format!("__nl_{}", self.nl_vars.len()), t.get_type());
        lemmas.push(Expr::Eq(Box::new(v.clone()), Box::new(t.clone())));
        self.nl_vars.insert(t.clone(), v.clone());
        v
    }

    /// Lemmas that cut off a model in which some `m != x * y` (Cimatti et al., ACM TOCL 2018,
    /// DOI 10.1145/3230639): sign rules and tangent planes at the model point. All are valid for
    /// every model of the original problem.
    fn nonlinear_lemmas(&mut self, model: &BTreeMap<String, ModelValue>) -> Vec<Expr> {
        use num_traits::Zero;
        let value = |e: &Expr| -> Option<BigRational> {
            match crate::eval::eval(e, model)? {
                crate::eval::Value::Num(r) => Some(r),
                _ => None,
            }
        };
        let monomials = self.lin.monomials().to_vec();
        let mut out = Vec::new();
        let zero = Expr::Int(0);
        let gt = |a: &Expr, b: &Expr| Expr::Gt(Box::new(a.clone()), Box::new(b.clone()));
        let lt = |a: &Expr, b: &Expr| Expr::Lt(Box::new(a.clone()), Box::new(b.clone()));
        let eq = |a: &Expr, b: &Expr| Expr::Eq(Box::new(a.clone()), Box::new(b.clone()));
        let le = |a: &Expr, b: &Expr| Expr::Le(Box::new(a.clone()), Box::new(b.clone()));
        let ge = |a: &Expr, b: &Expr| Expr::Ge(Box::new(a.clone()), Box::new(b.clone()));
        let imp = |p: Expr, q: Expr| Expr::Or(vec![Expr::Not(Box::new(p)), q]);
        // Monotonicity between pairs of monomials (instantiated once per pair, only while some
        // monomial is violated): for squares, x >= u >= 0 gives x*x >= u*u (and the mirror
        // image for non-positive values); with a shared factor z, a >= b gives z*a >= z*b when
        // z >= 0 and the reverse when z <= 0. All are valid in the reals.
        let violated = monomials.iter().any(|mono| {
            let m = Expr::Var(mono.name.clone(), Type::Real);
            match (value(&mono.x), value(&mono.y), value(&m)) {
                (Some(vx), Some(vy), Some(vm)) => vm != &vx * &vy,
                _ => false,
            }
        });
        if violated {
            let mono_var = |mono: &crate::theory::linarith::Monomial| {
                if mono.x.get_type() == Type::Int && mono.y.get_type() == Type::Int {
                    Expr::Var(mono.name.clone(), Type::Int)
                } else {
                    Expr::Var(mono.name.clone(), Type::Real)
                }
            };
            for (i, m1) in monomials.iter().enumerate() {
                for m2 in monomials.iter().skip(i + 1).take(60) {
                    let (e1, e2) = (mono_var(m1), mono_var(m2));
                    let mut pair: Vec<Expr> = Vec::new();
                    for (a, b, ea, eb) in [(m1, m2, &e1, &e2), (m2, m1, &e2, &e1)] {
                        if a.x == a.y && b.x == b.y {
                            let (x, u) = (&a.x, &b.x);
                            pair.push(imp(Expr::And(vec![ge(x, u), ge(u, &zero)]), ge(ea, eb)));
                            pair.push(imp(Expr::And(vec![gt(x, u), ge(u, &zero)]), gt(ea, eb)));
                            pair.push(imp(Expr::And(vec![le(x, u), le(u, &zero)]), ge(ea, eb)));
                            pair.push(imp(Expr::And(vec![lt(x, u), le(u, &zero)]), gt(ea, eb)));
                        }
                        for (za, fa) in [(&a.x, &a.y), (&a.y, &a.x)] {
                            for (zb, fb) in [(&b.x, &b.y), (&b.y, &b.x)] {
                                if za == zb && a.x != a.y && b.x != b.y {
                                    pair.push(imp(
                                        Expr::And(vec![ge(za, &zero), ge(fa, fb)]),
                                        ge(ea, eb),
                                    ));
                                    pair.push(imp(
                                        Expr::And(vec![le(za, &zero), ge(fa, fb)]),
                                        le(ea, eb),
                                    ));
                                    pair.push(imp(
                                        Expr::And(vec![gt(za, &zero), gt(fa, fb)]),
                                        gt(ea, eb),
                                    ));
                                }
                            }
                        }
                    }
                    for l in pair {
                        if self.nl_done.insert(l.clone()) {
                            out.push(l);
                        }
                    }
                }
            }
        }
        for mono in monomials {
            let m = Expr::Var(mono.name.clone(), mono.x.get_type());
            let m = if mono.x.get_type() == Type::Int && mono.y.get_type() == Type::Int {
                m
            } else {
                Expr::Var(mono.name.clone(), Type::Real)
            };
            let (Some(vx), Some(vy), Some(vm)) = (value(&mono.x), value(&mono.y), value(&m)) else {
                continue;
            };
            if std::env::var_os("RZ3_QDEBUG").is_some() {
                eprintln!("NL {}: x={} y={} m={}", mono.name, vx, vy, vm);
            }
            if vm == &vx * &vy {
                continue;
            }
            if self.nl_sign_done.insert(mono.name.clone()) {
                let (x, y) = (&mono.x, &mono.y);
                out.push(imp(
                    Expr::And(vec![gt(x, &zero), gt(y, &zero)]),
                    gt(&m, &zero),
                ));
                out.push(imp(
                    Expr::And(vec![lt(x, &zero), lt(y, &zero)]),
                    gt(&m, &zero),
                ));
                out.push(imp(
                    Expr::And(vec![gt(x, &zero), lt(y, &zero)]),
                    lt(&m, &zero),
                ));
                out.push(imp(
                    Expr::And(vec![lt(x, &zero), gt(y, &zero)]),
                    lt(&m, &zero),
                ));
                out.push(imp(eq(x, &zero), eq(&m, &zero)));
                out.push(imp(eq(y, &zero), eq(&m, &zero)));
                out.push(imp(
                    eq(&m, &zero),
                    Expr::Or(vec![eq(x, &zero), eq(y, &zero)]),
                ));
                if x == y {
                    out.push(ge(&m, &zero));
                }
            }
            // Tangent planes at (a, b): (x-a)(y-b) has the sign dictated by the sides. Points
            // are rounded to a coarse grid, refined only when the coarse lemma was already used:
            // tangents at the raw model point square the size of the numbers every round.
            let (x, y) = (&mono.x, &mono.y);
            for bits in [4u32, 10, 20, 40, 0] {
                let (a, b) = if bits == 0 {
                    (vx.clone(), vy.clone())
                } else {
                    (grid_point(&vx, bits), grid_point(&vy, bits))
                };
                let (ae, be) = (Expr::from_rational(&a), Expr::from_rational(&b));
                let plane = Expr::Add(vec![
                    Expr::Mul(vec![be.clone(), x.clone()]),
                    Expr::Mul(vec![ae.clone(), y.clone()]),
                    Expr::from_rational(&-(&a * &b)),
                ]);
                let same_side = Expr::Or(vec![
                    Expr::And(vec![le(x, &ae), le(y, &be)]),
                    Expr::And(vec![ge(x, &ae), ge(y, &be)]),
                ]);
                let opposite = Expr::Or(vec![
                    Expr::And(vec![le(x, &ae), ge(y, &be)]),
                    Expr::And(vec![ge(x, &ae), le(y, &be)]),
                ]);
                let l1 = imp(same_side, ge(&m, &plane));
                let l2 = imp(opposite, le(&m, &plane));
                if self.nl_done.insert(l1.clone()) | self.nl_done.insert(l2.clone()) {
                    out.push(l1);
                    out.push(l2);
                    break;
                }
            }
            // McCormick envelope over the bounds currently asserted on x and y.
            let (xl, xu) = self.lin.var_bounds(&var_name(x));
            let (yl, yu) = self.lin.var_bounds(&var_name(y));
            if let (Some(xl), Some(xu), Some(yl), Some(yu)) = (xl, xu, yl, yu) {
                let (xl, xu, yl, yu) = (xl.to_big(), xu.to_big(), yl.to_big(), yu.to_big());
                let k = |q: &BigRational| Expr::from_rational(q);
                let premise = Expr::And(vec![
                    ge(x, &k(&xl)),
                    le(x, &k(&xu)),
                    ge(y, &k(&yl)),
                    le(y, &k(&yu)),
                ]);
                // m >= lx*y + ly*x - lx*ly and m >= ux*y + uy*x - ux*uy
                let low1 = Expr::Add(vec![
                    Expr::Mul(vec![k(&xl), y.clone()]),
                    Expr::Mul(vec![k(&yl), x.clone()]),
                    k(&-(&xl * &yl)),
                ]);
                let low2 = Expr::Add(vec![
                    Expr::Mul(vec![k(&xu), y.clone()]),
                    Expr::Mul(vec![k(&yu), x.clone()]),
                    k(&-(&xu * &yu)),
                ]);
                // m <= ux*y + ly*x - ux*ly and m <= lx*y + uy*x - lx*uy
                let up1 = Expr::Add(vec![
                    Expr::Mul(vec![k(&xu), y.clone()]),
                    Expr::Mul(vec![k(&yl), x.clone()]),
                    k(&-(&xu * &yl)),
                ]);
                let up2 = Expr::Add(vec![
                    Expr::Mul(vec![k(&xl), y.clone()]),
                    Expr::Mul(vec![k(&yu), x.clone()]),
                    k(&-(&xl * &yu)),
                ]);
                out.push(imp(premise.clone(), ge(&m, &low1)));
                out.push(imp(premise.clone(), ge(&m, &low2)));
                out.push(imp(premise.clone(), le(&m, &up1)));
                out.push(imp(premise, le(&m, &up2)));
            }
            let _ = BigRational::zero();
        }
        out
    }

    /// Feed the arrays / strings / floating-point / quantifier / nonlinear / equality
    /// theories the atoms of the current SAT assignment. Nothing runs, and nothing is
    /// cloned, when none of that content is present.
    fn check_other_theories(&mut self) -> OtherTheories {
        if !self.slow && self.nla_atoms.is_empty() {
            return OtherTheories::Consistent;
        }
        self.euf.reset();
        self.array.reset();
        self.quant.reset();
        self.string.reset();
        self.nla.reset();
        self.fp.reset();

        let assigned_atoms = self
            .expr_to_lit
            .iter()
            .filter_map(|(expr, &lit)| match self.sat_solver.get_lit_value(lit) {
                crate::sat::Assignment::True => Some((expr.clone(), true)),
                crate::sat::Assignment::False => Some((expr.clone(), false)),
                _ => None,
            })
            .collect::<Vec<_>>();
        for (expr, is_true) in assigned_atoms {
            let a = if is_true {
                expr.clone()
            } else {
                Expr::Not(Box::new(expr.clone()))
            };
            if self.slow {
                if let Some(euf_expr) = self.euf_assignment_assertion(&expr, is_true) {
                    self.euf.assert(&euf_expr);
                } else {
                    self.euf.assert(&a);
                }
                self.array.assert(&a);
                self.quant.assert(&a);
                self.string.assert(&a);
                self.fp.assert(&a);
            }
            if expr.has_unhandled_nonlinear() {
                self.nla.assert(&a);
            }
        }

        let euf_ok = self.euf.check();
        let array_ok = self.array.check();
        let string_ok = self.string.check();
        if self.string.is_unknown() {
            return OtherTheories::Unknown;
        }
        let nla_ok = self.nla.check();
        if self.nla.is_unknown() {
            return OtherTheories::Unknown;
        }
        let fp_ok = self.fp.check();
        if euf_ok && array_ok && string_ok && nla_ok && fp_ok {
            return OtherTheories::Consistent;
        }

        let mut explanation_found = false;
        let mut learn = |this: &mut Self, name: &str, conflict: Vec<Expr>| {
            if !conflict.is_empty() {
                this.proof_gen
                    .add_step(crate::proof::ProofStep::TheoryLemma(
                        conflict.clone(),
                        name.to_string(),
                    ));
                if this.learn_conflict(&conflict) {
                    explanation_found = true;
                }
            }
        };
        if !euf_ok {
            let c = self.euf.explain();
            learn(self, "EUF", c);
        }
        if !nla_ok {
            let c = self.nla.explain();
            learn(self, "NLA", c);
        }
        if !fp_ok {
            let c = self.fp.explain();
            learn(self, "FP", c);
        }
        if explanation_found {
            return OtherTheories::Refuted;
        }
        // No usable explanation: block exactly this assignment so the search progresses.
        let mut clause = Vec::new();
        for &lit in self.expr_to_lit.values() {
            match self.sat_solver.get_lit_value(lit) {
                crate::sat::Assignment::True => clause.push(-lit),
                crate::sat::Assignment::False => clause.push(lit),
                _ => {}
            }
        }
        if clause.is_empty() {
            OtherTheories::Unsat
        } else {
            let _ = self.sat_solver.add_clause(clause);
            OtherTheories::Refuted
        }
    }

    fn euf_assignment_assertion(&self, expr: &Expr, is_true: bool) -> Option<Expr> {
        match expr {
            Expr::Var(_, _) | Expr::App(_, _) if self.infer_type(expr) == Some(Type::Bool) => Some(
                Expr::Eq(Box::new(expr.clone()), Box::new(Expr::Bool(is_true))),
            ),
            _ => None,
        }
    }

    fn learn_conflict(&mut self, conflict: &[Expr]) -> bool {
        self.stats.theory_conflicts += 1;
        if conflict.is_empty() {
            return false;
        }
        let mut clause = Vec::new();
        for expr in conflict {
            if let Some(&lit) = self.expr_to_lit.get(expr) {
                clause.push(-lit);
            } else if let Expr::Not(inner) = expr {
                if let Some(&lit) = self.expr_to_lit.get(inner) {
                    clause.push(lit);
                }
            } else if let Expr::Eq(atom, value) = expr {
                // EUF sees a Boolean atom as `atom = true/false` (see
                // `euf_assignment_assertion`); map that back to the atom's literal.
                if let (Some(&lit), Expr::Bool(b)) = (self.expr_to_lit.get(&**atom), &**value) {
                    clause.push(if *b { -lit } else { lit });
                }
            }
        }
        // A conflict that maps to no literal cannot refute the current assignment.
        // Report that, so the caller blocks the assignment instead of looping on it.
        if clause.is_empty() || clause.len() < conflict.len() {
            return false;
        }
        let _ = self.sat_solver.add_clause(clause);
        true
    }
}
