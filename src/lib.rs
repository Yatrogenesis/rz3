pub mod ast;
pub mod sat;
pub mod theory;
pub mod parser;
pub mod tactic;
pub mod proof;

use crate::sat::CdclSolver;
use crate::theory::{LraSolver, EufSolver, TheorySolver, ArraySolver, QuantifierSolver, StringSolver, NlaSolver};
use crate::tactic::{Simplifier, TacticEngine, SolveEqs};
use std::collections::BTreeMap;
use crate::ast::{Expr, Type, ModelValue};
use num_traits::ToPrimitive;

pub enum SolverResult {
    Sat,
    Unsat,
    Unknown,
}

pub struct Rz3Solver {
    sat_solver: CdclSolver,
    expr_to_lit: BTreeMap<Expr, i32>,
    lit_to_expr: BTreeMap<i32, Expr>,
    bv_vars: BTreeMap<(String, usize), i32>,
    bv_expr_to_bits: BTreeMap<Expr, Vec<i32>>,
    next_sat_var: i32,
    symbol_table: BTreeMap<String, Type>,
    tactic_engine: TacticEngine,

    lra: LraSolver,
    euf: EufSolver,
    array: ArraySolver,
    quant: QuantifierSolver,
    string: StringSolver,
    nla: NlaSolver,
    proof_gen: crate::proof::Proof,

    /// All asserted expressions in order — used for push/pop rebuild.
    assertion_history: Vec<Expr>,
    /// Stack of assertion_history lengths at each push() call.
    scope_stack: Vec<usize>,
}

impl Default for Rz3Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Rz3Solver {
    pub fn new() -> Self {
        let mut tactic_engine = TacticEngine::new();
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
            lra: LraSolver::new(),
            euf: EufSolver::new(),
            array: ArraySolver::new(),
            quant: QuantifierSolver::new(),
            string: StringSolver::new(),
            nla: NlaSolver::new(),
            proof_gen: crate::proof::Proof::new(),
            assertion_history: Vec::new(),
            scope_stack: Vec::new(),
        }
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
        te.add_tactic(Box::new(Simplifier));
        te.add_tactic(Box::new(SolveEqs));
        self.tactic_engine = te;
        self.lra = LraSolver::new();
        self.euf = EufSolver::new();
        self.array = ArraySolver::new();
        self.quant = QuantifierSolver::new();
        self.string = StringSolver::new();
        self.nla = NlaSolver::new();
        self.proof_gen = crate::proof::Proof::new();

        self.symbol_table = sym;
        self.assertion_history = history;
        self.scope_stack = scopes;

        for expr in self.assertion_history.clone() {
            self.assert_no_track(&expr);
        }
    }

    fn assert_no_track(&mut self, expr: &Expr) {
        let simplified = self.tactic_engine.apply(expr.clone());
        if let Expr::Bool(true) = simplified { return; }
        if let Expr::Bool(false) = simplified {
            self.sat_solver.ok = false;
            return;
        }
        self.lra.assert(&simplified);
        self.euf.assert(&simplified);
        self.array.assert(&simplified);
        self.quant.assert(&simplified);
        self.string.assert(&simplified);
        self.nla.assert(&simplified);
        let lit = self.tseitin(&simplified);
        let _ = self.sat_solver.add_clause(vec![lit]);
    }

    pub fn declare_fun(&mut self, name: String, ty: Type) {
        self.symbol_table.insert(name, ty);
    }

    pub fn get_model(&self) -> BTreeMap<String, ModelValue> {
        let mut model = BTreeMap::new();

        // Bool variables from SAT assignments
        for (expr, &lit) in &self.expr_to_lit {
            if let Expr::Var(name, ty) = expr {
                let val = matches!(self.sat_solver.get_lit_value(lit), crate::sat::Assignment::True);
                let mv = match ty {
                    crate::ast::Type::Bool => ModelValue::Bool(val),
                    _ => continue,
                };
                model.insert(name.clone(), mv);
            }
        }

        // Bit-vector variables
        for ((name, bit), &lit) in &self.bv_vars {
            let val = match self.sat_solver.get_lit_value(lit) {
                crate::sat::Assignment::True => 1u64,
                _ => 0u64,
            };
            let entry = model.entry(name.clone()).or_insert(ModelValue::BitVec(0, 0));
            if let ModelValue::BitVec(curr, width) = entry {
                *curr |= val << bit;
                *width = (*width).max(bit + 1);
            }
        }

        // Real/Int variables from LRA simplex assignments
        for (name, val) in self.lra.get_all_assignments() {
            model.entry(name.clone()).or_insert_with(|| {
                match self.symbol_table.get(&name) {
                    Some(crate::ast::Type::Int) => ModelValue::Int(val.to_integer().to_i64().unwrap_or(0)),
                    _ => ModelValue::Real(val),
                }
            });
        }

        model
    }

    fn get_or_create_lit(&mut self, expr: &Expr) -> i32 {
        if let Some(&lit) = self.expr_to_lit.get(expr) {
            lit
        } else {
            let lit = self.next_sat_var;
            self.next_sat_var += 1;
            self.expr_to_lit.insert(expr.clone(), lit);
            self.lit_to_expr.insert(lit, expr.clone());
            lit
        }
    }

    fn is_bv(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Var(_, crate::ast::Type::BitVec(_)) | Expr::BvConst(_, _) | Expr::BvAdd(_, _) | Expr::BvSub(_, _) | Expr::BvMul(_, _) |
            Expr::BvAnd(_, _) | Expr::BvOr(_, _) | Expr::BvXor(_, _) |
            Expr::BvNot(_) | Expr::BvShl(_, _) | Expr::BvLshr(_, _) |
            Expr::BvAshr(_, _) | Expr::BvExtract(_, _, _) | Expr::BvConcat(_, _))
    }

    pub fn assert(&mut self, expr: &Expr) {
        self.assertion_history.push(expr.clone());
        self.assert_no_track(expr);
    }

    fn tseitin(&mut self, expr: &Expr) -> i32 {
        match expr {
            Expr::ForAll(_, _) | Expr::Select(_, _) | Expr::Store(_, _, _) => self.get_or_create_lit(expr),
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
            Expr::Lt(_a, _b) | Expr::Gt(_a, _b) => {
                self.get_or_create_lit(expr)
            }
            Expr::Eq(a, b) => {
                if self.is_bv(a) || self.is_bv(b) {
                    let mut blaster = crate::theory::bv::BitBlaster::new(
                        &mut self.sat_solver,
                        &mut self.bv_vars,
                        &mut self.bv_expr_to_bits,
                        &mut self.next_sat_var,
                    );
                    let bits_a = blaster.bit_blast(a);
                    let bits_b = blaster.bit_blast(b);
                    let res_lit = self.get_or_create_lit(expr);
                    
                    let mut bit_eqs = Vec::new();
                    for (la, lb) in bits_a.into_iter().zip(bits_b) {
                        let eq = self.next_sat_var;
                        self.next_sat_var += 1;
                        self.sat_solver.add_clause(vec![-la, lb, -eq]);
                        self.sat_solver.add_clause(vec![la, -lb, -eq]);
                        self.sat_solver.add_clause(vec![la, lb, eq]);
                        self.sat_solver.add_clause(vec![-la, -lb, eq]);
                        bit_eqs.push(eq);
                    }
                    
                    for &eq in &bit_eqs {
                        self.sat_solver.add_clause(vec![-res_lit, eq]);
                    }
                    let mut final_clause = bit_eqs.iter().map(|&l| -l).collect::<Vec<_>>();
                    final_clause.push(res_lit);
                    self.sat_solver.add_clause(final_clause);
                    res_lit
                } else if a.get_type() == Type::Bool {
                    let res_lit = self.get_or_create_lit(expr);
                    let lit_a = self.tseitin(a);
                    let lit_b = self.tseitin(b);
                    self.sat_solver.add_clause(vec![lit_a, -lit_b, -res_lit]);
                    self.sat_solver.add_clause(vec![-lit_a, lit_b, -res_lit]);
                    self.sat_solver.add_clause(vec![-lit_a, -lit_b, res_lit]);
                    self.sat_solver.add_clause(vec![lit_a, lit_b, res_lit]);
                    res_lit
                } else {
                    self.get_or_create_lit(expr)
                }
            }
            _ => {
                self.get_or_create_lit(expr)
            }
        }
    }

    pub fn check(&mut self) -> SolverResult {
        loop {
            if !self.sat_solver.solve() {
                return SolverResult::Unsat;
            }

            self.lra.reset();
            self.euf.reset();
            self.array.reset();
            self.quant.reset();
            self.string.reset();
            self.nla.reset();
            
            for (expr, &lit) in &self.expr_to_lit {
                let assign = self.sat_solver.get_lit_value(lit);
                let atom = match assign {
                    crate::sat::Assignment::True => Some(expr.clone()),
                    crate::sat::Assignment::False => Some(Expr::Not(Box::new(expr.clone()))),
                    _ => None,
                };

                if let Some(a) = atom {
                    self.lra.assert(&a);
                    self.euf.assert(&a);
                    self.array.assert(&a);
                    self.quant.assert(&a);
                    self.string.assert(&a);
                    self.nla.assert(&a);
                }
            }

            let lra_ok = self.lra.check();
            if self.lra.is_unknown() {
                return SolverResult::Unknown;
            }
            let euf_ok = self.euf.check();
            let array_ok = self.array.check();
            let string_ok = self.string.check();
            let nla_ok = self.nla.check();

            if lra_ok && euf_ok && array_ok && string_ok && nla_ok {
                let model = self.get_model();
                let array_lemmas = self.array.generate_lemmas();
                let quant_lemmas = self.quant.generate_lemmas(&mut self.euf, &model);
                let string_lemmas = self.string.generate_lemmas();
                if array_lemmas.is_empty() && quant_lemmas.is_empty() && string_lemmas.is_empty() {
                    return SolverResult::Sat;
                } else {
                    for lemma in array_lemmas.into_iter()
                        .chain(quant_lemmas)
                        .chain(string_lemmas) {
                        self.assert(&lemma);
                    }
                    continue;
                }
            } else {
                let mut explanation_found = false;
                if !lra_ok {
                    let conflict = self.lra.explain();
                    if !conflict.is_empty() {
                        self.proof_gen.add_step(crate::proof::ProofStep::TheoryLemma(conflict.clone(), "LRA".to_string()));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }
                if !euf_ok {
                    let conflict = self.euf.explain();
                    if !conflict.is_empty() {
                        self.proof_gen.add_step(crate::proof::ProofStep::TheoryLemma(conflict.clone(), "EUF".to_string()));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }
                if !nla_ok {
                    let conflict = self.nla.explain();
                    if !conflict.is_empty() {
                        self.proof_gen.add_step(crate::proof::ProofStep::TheoryLemma(conflict.clone(), "NLA".to_string()));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }

                if !explanation_found {
                    let mut clause = Vec::new();
                    for &lit in self.expr_to_lit.values() {
                         let val = self.sat_solver.get_lit_value(lit);
                         if val == crate::sat::Assignment::True {
                             clause.push(-lit);
                         } else if val == crate::sat::Assignment::False {
                             clause.push(lit);
                         }
                    }
                    if !clause.is_empty() {
                        let _ = self.sat_solver.add_clause(clause);
                    } else {
                        return SolverResult::Unsat;
                    }
                }
            }
        }
    }

    fn learn_conflict(&mut self, conflict: &[Expr]) {
        if conflict.is_empty() { return; }
        let mut clause = Vec::new();
        for expr in conflict {
            if let Some(&lit) = self.expr_to_lit.get(expr) {
                clause.push(-lit);
            } else if let Expr::Not(inner) = expr {
                if let Some(&lit) = self.expr_to_lit.get(inner) {
                    clause.push(lit);
                }
            }
        }
        if !clause.is_empty() {
            let _ = self.sat_solver.add_clause(clause);
        }
    }
}
