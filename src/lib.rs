pub mod ast;
pub mod parser;
pub mod proof;
pub mod sat;
pub mod tactic;
pub mod theory;

use crate::ast::{Expr, ModelValue, Type};
use crate::sat::CdclSolver;
use crate::tactic::{Simplifier, SolveEqs, TacticEngine};
use crate::theory::fp::FpSolver;
use crate::theory::{
    ArraySolver, EufSolver, LraSolver, NlaSolver, QuantifierSolver, StringSolver, TheorySolver,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    fp: FpSolver,
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
            fp: FpSolver::new(),
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
        self.fp = FpSolver::new();
        self.proof_gen = crate::proof::Proof::new();

        self.symbol_table = sym;
        self.assertion_history = history;
        self.scope_stack = scopes;

        for expr in self.assertion_history.clone() {
            self.assert_no_track(&expr);
        }
    }

    fn assert_no_track(&mut self, expr: &Expr) {
        let typed = self.resolve_expr_types(expr);
        let simplified = self.tactic_engine.apply(typed);
        if let Expr::Bool(true) = simplified {
            return;
        }
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
        self.fp.assert(&simplified);
        let lit = self.tseitin(&simplified);
        let _ = self.sat_solver.add_clause(vec![lit]);
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
            let val = match self.sat_solver.get_lit_value(lit) {
                crate::sat::Assignment::True => 1u64,
                _ => 0u64,
            };
            let entry = model
                .entry(name.clone())
                .or_insert(ModelValue::BitVec(0, 0));
            if let ModelValue::BitVec(curr, width) = entry {
                *curr |= val << bit;
                *width = (*width).max(bit + 1);
            }
        }

        // Real/Int variables from LRA simplex assignments
        for (name, val) in self.lra.get_all_assignments() {
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
        self.fp
            .get_model_value(&typed)
            .or_else(|| self.lra.get_model_value(&typed))
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
            Expr::BvConst(value, width) => Some(ModelValue::BitVec(*value, *width)),
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
            lit
        }
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
                } else if self.infer_type(a) == Some(Type::Bool) {
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
            _ => self.get_or_create_lit(expr),
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
                let euf_a = self.euf_assignment_assertion(&expr, is_true);

                self.lra.assert(&a);
                if let Some(euf_expr) = euf_a {
                    self.euf.assert(&euf_expr);
                } else {
                    self.euf.assert(&a);
                }
                self.array.assert(&a);
                self.quant.assert(&a);
                self.string.assert(&a);
                self.nla.assert(&a);
                self.fp.assert(&a);
            }

            let lra_ok = self.lra.check();
            if self.lra.is_unknown() {
                return SolverResult::Unknown;
            }
            let euf_ok = self.euf.check();
            let array_ok = self.array.check();
            let string_ok = self.string.check();
            let nla_ok = self.nla.check();
            let fp_ok = self.fp.check();

            if lra_ok && euf_ok && array_ok && string_ok && nla_ok && fp_ok {
                let model = self.get_model();
                let array_lemmas = self.array.generate_lemmas();
                let quant_lemmas = self.quant.generate_lemmas(&mut self.euf, &model);
                let string_lemmas = self.string.generate_lemmas();
                if array_lemmas.is_empty() && quant_lemmas.is_empty() && string_lemmas.is_empty() {
                    return SolverResult::Sat;
                } else {
                    for lemma in array_lemmas
                        .into_iter()
                        .chain(quant_lemmas)
                        .chain(string_lemmas)
                    {
                        self.assert(&lemma);
                    }
                    continue;
                }
            } else {
                let mut explanation_found = false;
                if !lra_ok {
                    let conflict = self.lra.explain();
                    if !conflict.is_empty() {
                        self.proof_gen
                            .add_step(crate::proof::ProofStep::TheoryLemma(
                                conflict.clone(),
                                "LRA".to_string(),
                            ));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }
                if !euf_ok {
                    let conflict = self.euf.explain();
                    if !conflict.is_empty() {
                        self.proof_gen
                            .add_step(crate::proof::ProofStep::TheoryLemma(
                                conflict.clone(),
                                "EUF".to_string(),
                            ));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }
                if !nla_ok {
                    let conflict = self.nla.explain();
                    if !conflict.is_empty() {
                        self.proof_gen
                            .add_step(crate::proof::ProofStep::TheoryLemma(
                                conflict.clone(),
                                "NLA".to_string(),
                            ));
                        self.learn_conflict(&conflict);
                        explanation_found = true;
                    }
                }
                if !fp_ok {
                    let conflict = self.fp.explain();
                    if !conflict.is_empty() {
                        self.proof_gen
                            .add_step(crate::proof::ProofStep::TheoryLemma(
                                conflict.clone(),
                                "FP".to_string(),
                            ));
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

    fn euf_assignment_assertion(&self, expr: &Expr, is_true: bool) -> Option<Expr> {
        match expr {
            Expr::Var(_, _) | Expr::App(_, _) if self.infer_type(expr) == Some(Type::Bool) => Some(
                Expr::Eq(Box::new(expr.clone()), Box::new(Expr::Bool(is_true))),
            ),
            _ => None,
        }
    }

    fn learn_conflict(&mut self, conflict: &[Expr]) {
        if conflict.is_empty() {
            return;
        }
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
