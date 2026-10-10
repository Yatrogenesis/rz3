use crate::ast::{Expr, ModelValue, Type};
use crate::theory::euf::{EufSolver, Node};
use crate::theory::TheorySolver;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use std::collections::{BTreeMap, BTreeSet};

pub struct QuantifierSolver {
    quantifiers: Vec<Expr>,
    ground_terms: BTreeSet<Expr>,
    instantiations: BTreeSet<Expr>,
    pattern_index: BTreeMap<String, Vec<usize>>,
}

impl QuantifierSolver {
    /// A live `ForAll` can never be CERTIFIED sat by finite E-matching/MBQI
    /// instantiation — reaching a lemma fixpoint only means "no
    /// counterexample found among the ground terms explored", not "true
    /// over the whole domain". The top-level solver consults this right
    /// before it would otherwise declare Sat (see RZ3-2: `check()` on this
    /// theory was a bare `{ true }` and its result was never even consulted).
    pub fn is_unknown(&self) -> bool {
        !self.quantifiers.is_empty()
    }
}

impl Default for QuantifierSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl QuantifierSolver {
    pub fn new() -> Self {
        Self {
            quantifiers: Vec::new(),
            ground_terms: BTreeSet::new(),
            instantiations: BTreeSet::new(),
            pattern_index: BTreeMap::new(),
        }
    }

    pub fn reset(&mut self) {
        self.quantifiers.clear();
        self.ground_terms.clear();
        self.pattern_index.clear();
    }

    fn collect_ground_terms(&mut self, expr: &Expr, euf: &EufSolver) {
        match expr {
            Expr::App(name, args) => {
                if let Some(id) = euf.get_id_public(expr) {
                    self.pattern_index.entry(name.clone()).or_default().push(id);
                }
                for arg in args {
                    self.collect_ground_terms(arg, euf);
                }
            }
            Expr::Select(a, i) => {
                if let Some(id) = euf.get_id_public(expr) {
                    self.pattern_index
                        .entry("select".to_string())
                        .or_default()
                        .push(id);
                }
                self.collect_ground_terms(a, euf);
                self.collect_ground_terms(i, euf);
            }
            _ => {}
        }
    }

    pub fn generate_lemmas(
        &mut self,
        euf: &mut EufSolver,
        model: &BTreeMap<String, ModelValue>,
    ) -> Vec<Expr> {
        let mut lemmas = Vec::new();
        self.pattern_index.clear();
        let n_ids = euf.get_num_ids();
        for id in 0..n_ids {
            let expr = euf.get_expr(id).clone();
            self.collect_ground_terms(&expr, euf);
            self.ground_terms.insert(expr);
        }

        for q_expr in &self.quantifiers {
            if let Expr::ForAll(vars, body) = q_expr {
                // Instanciar con ground terms conocidos (MBQI robusto)
                for (name, _ty) in vars {
                    if !model.contains_key(name) {
                        for term in &self.ground_terms {
                            let mut sub = BTreeMap::new();
                            sub.insert(name.clone(), term.clone());
                            let instantiated = body.substitute(&sub);
                            let lemma =
                                Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                            if self.instantiations.insert(lemma.clone()) {
                                lemmas.push(lemma);
                            }
                        }
                    }
                }

                // MBQI: Instanciación basada en modelo si es falso
                if !self.evaluate_quantifier(q_expr, model) {
                    let mut sub = BTreeMap::new();
                    for (name, ty) in vars {
                        if let Some(val) = model.get(name) {
                            if let Some(expr) = self.model_val_to_expr(val, ty) {
                                sub.insert(name.clone(), expr);
                            }
                        }
                    }
                    let instantiated = body.substitute(&sub);
                    let lemma = Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                    if self.instantiations.insert(lemma.clone()) {
                        lemmas.push(lemma);
                    }
                }

                // E-matching
                let patterns = self.infer_patterns(body, vars);
                for pattern in patterns {
                    let mut substitutions = Vec::new();
                    self.match_pattern(
                        &pattern,
                        vars,
                        euf,
                        &mut BTreeMap::new(),
                        &mut substitutions,
                    );
                    for sub in substitutions {
                        let instantiated = body.substitute(&sub);
                        let lemma = Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                        if self.instantiations.insert(lemma.clone()) {
                            lemmas.push(lemma);
                        }
                    }
                }
            }
        }
        lemmas
    }

    fn evaluate_quantifier(&self, expr: &Expr, model: &BTreeMap<String, ModelValue>) -> bool {
        match expr {
            Expr::ForAll(vars, body) => {
                let mut sub = BTreeMap::new();
                for (name, ty) in vars {
                    if let Some(val) = model.get(name) {
                        if let Some(expr) = self.model_val_to_expr(val, ty) {
                            sub.insert(name.clone(), expr);
                        }
                    }
                }
                let instantiated = body.substitute(&sub);
                match self.evaluate_expr(&instantiated, model) {
                    Some(ModelValue::Bool(b)) => b,
                    _ => true,
                }
            }
            _ => true,
        }
    }

    fn evaluate_expr(
        &self,
        expr: &Expr,
        model: &BTreeMap<String, ModelValue>,
    ) -> Option<ModelValue> {
        match expr {
            Expr::Var(name, _) => model.get(name).cloned(),
            Expr::Bool(b) => Some(ModelValue::Bool(*b)),
            Expr::Int(i) => Some(ModelValue::Int(BigInt::from(*i))),
            Expr::Real(i, s) => Some(ModelValue::Real(BigRational::new(
                BigInt::from(*i),
                BigInt::from(10u8).pow(*s),
            ))),
            Expr::And(args) => {
                let mut res = true;
                for arg in args {
                    if let Some(ModelValue::Bool(b)) = self.evaluate_expr(arg, model) {
                        if !b {
                            res = false;
                            break;
                        }
                    } else {
                        return None;
                    }
                }
                Some(ModelValue::Bool(res))
            }
            Expr::Not(inner) => {
                if let Some(ModelValue::Bool(b)) = self.evaluate_expr(inner, model) {
                    Some(ModelValue::Bool(!b))
                } else {
                    None
                }
            }
            Expr::Eq(a, b) => {
                let ea = self.evaluate_expr(a, model);
                let eb = self.evaluate_expr(b, model);
                match (ea, eb) {
                    (Some(ModelValue::Int(va)), Some(ModelValue::Int(vb))) => {
                        Some(ModelValue::Bool(va == vb))
                    }
                    (Some(ModelValue::Real(va)), Some(ModelValue::Real(vb))) => {
                        Some(ModelValue::Bool(va == vb))
                    }
                    _ => None,
                }
            }
            Expr::App(name, _args) => model.get(name).cloned(),
            _ => None,
        }
    }

    fn model_val_to_expr(&self, val: &ModelValue, ty: &Type) -> Option<Expr> {
        match (val, ty) {
            (ModelValue::Bool(b), _) => Some(Expr::Bool(*b)),
            (ModelValue::Int(i), _) => i.to_i64().map(Expr::Int),
            (ModelValue::Real(r), _) if r.is_integer() => {
                r.to_integer().to_i64().map(|i| Expr::Real(i, 0))
            }
            _ => None,
        }
    }

    fn infer_patterns(&self, body: &Expr, vars: &[(String, Type)]) -> Vec<Expr> {
        let mut patterns = Vec::new();
        self.collect_apps(body, vars, &mut patterns);
        if patterns.is_empty() {
            patterns.push(body.clone());
        }
        patterns
    }

    fn collect_apps(&self, expr: &Expr, vars: &[(String, Type)], patterns: &mut Vec<Expr>) {
        match expr {
            Expr::App(_, _) | Expr::Select(_, _)
                if vars
                    .iter()
                    .any(|(vname, _)| self.uses_variable(expr, vname)) =>
            {
                patterns.push(expr.clone());
            }
            _ => {}
        }
    }

    fn uses_variable(&self, expr: &Expr, name: &str) -> bool {
        match expr {
            Expr::Var(n, _) => n == name,
            Expr::App(_, args) => args.iter().any(|a| self.uses_variable(a, name)),
            Expr::Select(a, i) => self.uses_variable(a, name) || self.uses_variable(i, name),
            _ => false,
        }
    }

    fn match_pattern(
        &self,
        pattern: &Expr,
        vars: &[(String, Type)],
        euf: &mut EufSolver,
        current_sub: &mut BTreeMap<String, Expr>,
        results: &mut Vec<BTreeMap<String, Expr>>,
    ) {
        if let Expr::App(name, _) = pattern {
            if let Some(candidates) = self.pattern_index.get(name) {
                let mut ctx = MatchContext { vars, euf, results };
                for &term_id in candidates {
                    let mut sub = current_sub.clone();
                    if self.match_recursive(pattern, term_id, &mut sub, &mut ctx)
                        && sub.len() == vars.len()
                    {
                        ctx.results.push(sub);
                    }
                }
            }
        }
    }

    fn match_recursive(
        &self,
        pattern: &Expr,
        term_id: usize,
        current_sub: &mut BTreeMap<String, Expr>,
        ctx: &mut MatchContext,
    ) -> bool {
        match pattern {
            Expr::Var(name, _) if ctx.vars.iter().any(|(v, _)| v == name) => {
                if let Some(existing) = current_sub.get(name) {
                    let Some(existing_id) = ctx.euf.get_id_public(existing) else {
                        return false;
                    };
                    return ctx.euf.find_public(existing_id) == ctx.euf.find_public(term_id);
                } else {
                    current_sub.insert(name.clone(), ctx.euf.get_expr(term_id).clone());
                    return true;
                }
            }
            Expr::App(p_name, p_args) => {
                let node = ctx.euf.get_node(term_id).clone();
                if let Node::App(t_name, t_args) = node {
                    if p_name == &t_name && p_args.len() == t_args.len() {
                        return self.match_args(p_args, &t_args, current_sub, ctx);
                    }
                }
            }
            _ => {
                if let Some(pid) = ctx.euf.get_id_public(pattern) {
                    return ctx.euf.find_public(pid) == ctx.euf.find_public(term_id);
                }
            }
        }
        false
    }

    fn match_args(
        &self,
        p_args: &[Expr],
        t_args: &[usize],
        current_sub: &mut BTreeMap<String, Expr>,
        ctx: &mut MatchContext,
    ) -> bool {
        if p_args.is_empty() {
            return true;
        }
        let mut sub = current_sub.clone();
        if self.match_recursive(&p_args[0], t_args[0], &mut sub, ctx)
            && self.match_args(&p_args[1..], &t_args[1..], &mut sub, ctx)
        {
            *current_sub = sub;
            return true;
        }
        false
    }
}

struct MatchContext<'a> {
    vars: &'a [(String, Type)],
    euf: &'a mut EufSolver,
    results: &'a mut Vec<BTreeMap<String, Expr>>,
}

impl TheorySolver for QuantifierSolver {
    fn assert(&mut self, expr: &Expr) {
        if let Expr::ForAll(_, _) = expr {
            self.quantifiers.push(expr.clone());
        }
    }
    fn check(&mut self) -> bool {
        true
    }
    fn explain(&self) -> Vec<Expr> {
        Vec::new()
    }
    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn b(e: Expr) -> Box<Expr> {
        Box::new(e)
    }
    fn iv(n: &str) -> Expr {
        Expr::Var(n.to_string(), Type::Int)
    }
    fn f(e: Expr) -> Expr {
        Expr::App("f".to_string(), vec![e])
    }
    fn eq(x: Expr, y: Expr) -> Expr {
        Expr::Eq(b(x), b(y))
    }
    fn forall_x(body: Expr) -> Expr {
        Expr::ForAll(vec![("x".to_string(), Type::Int)], b(body))
    }
    fn implies(q: &Expr, body: Expr) -> Expr {
        Expr::Implies(b(q.clone()), b(body))
    }
    fn int_model(name: &str, v: i64) -> BTreeMap<String, ModelValue> {
        let mut m = BTreeMap::new();
        m.insert(name.to_string(), ModelValue::Int(BigInt::from(v)));
        m
    }

    #[test]
    fn unknown_exactly_while_a_universal_is_live() {
        let mut q = QuantifierSolver::new();
        assert!(!q.is_unknown());
        q.assert(&Expr::Exists(
            vec![("x".to_string(), Type::Int)],
            b(Expr::Bool(true)),
        ));
        assert!(!q.is_unknown(), "only universals are tracked");
        q.assert(&forall_x(Expr::Bool(true)));
        assert!(q.is_unknown());
        assert!(q.check());
        assert!(q.explain().is_empty());
        q.ground_terms.insert(iv("a"));
        q.pattern_index.insert("f".to_string(), vec![0]);
        q.reset();
        assert!(!q.is_unknown());
        assert!(q.ground_terms.is_empty());
        assert!(q.pattern_index.is_empty());
    }

    #[test]
    fn ground_terms_and_patterns_are_collected_from_the_congruence_closure() {
        let mut euf = EufSolver::new();
        let mut q = QuantifierSolver::new();
        euf.assert(&eq(iv("a"), iv("c")));
        euf.assert(&eq(f(iv("a")), iv("b")));
        let sel = Expr::Select(
            b(Expr::Var(
                "m".to_string(),
                Type::Array(b_ty(Type::Int), b_ty(Type::Int)),
            )),
            b(iv("a")),
        );
        euf.assert(&eq(sel.clone(), iv("b")));
        q.generate_lemmas(&mut euf, &BTreeMap::new());
        let fa = euf.get_id_public(&f(iv("a"))).unwrap();
        let sid = euf.get_id_public(&sel).unwrap();
        assert_eq!(q.pattern_index.get("f"), Some(&vec![fa]));
        assert_eq!(q.pattern_index.get("select"), Some(&vec![sid]));
        assert!(q.ground_terms.contains(&f(iv("a"))));
        assert!(q.ground_terms.contains(&iv("c")));
    }

    fn b_ty(t: Type) -> Box<Type> {
        Box::new(t)
    }

    #[test]
    fn universal_is_instantiated_on_ground_terms_and_by_matching() {
        let mut euf = EufSolver::new();
        euf.assert(&eq(iv("a"), iv("a")));
        euf.assert(&eq(f(iv("a")), iv("b")));
        let mut q = QuantifierSolver::new();
        let body = eq(f(iv("x")), Expr::Int(0));
        let all = forall_x(body.clone());
        q.assert(&all);
        let lemmas = q.generate_lemmas(&mut euf, &BTreeMap::new());
        // One instance per ground term (a, f(a), b).
        let n_ground = q.ground_terms.len();
        assert_eq!(n_ground, 3);
        assert_eq!(lemmas.len(), 3);
        let at_a = implies(&all, eq(f(iv("a")), Expr::Int(0)));
        assert_eq!(lemmas.iter().filter(|l| **l == at_a).count(), 1);
        // A second round finds nothing new.
        assert!(q.generate_lemmas(&mut euf, &BTreeMap::new()).is_empty());
    }

    #[test]
    fn a_variable_with_a_model_value_is_not_instantiated_on_ground_terms() {
        let p = |e: Expr| Expr::App("p".to_string(), vec![e]);
        let mut euf = EufSolver::new();
        // Arguments first: see the ignored id-aliasing test in euf.rs.
        euf.assert(&eq(iv("a"), iv("a")));
        euf.assert(&eq(p(iv("a")), Expr::Bool(true)));
        let mut q = QuantifierSolver::new();
        let all = forall_x(p(iv("x")));
        q.assert(&all);
        // x has a model value: only E-matching contributes (p(a) matches the pattern p(x)).
        let lemmas = q.generate_lemmas(&mut euf, &int_model("x", 1));
        assert_eq!(lemmas, vec![implies(&all, p(iv("a")))]);
        // Without a model value every ground term (a, p(a), true) is tried as well.
        let mut q = QuantifierSolver::new();
        q.assert(&all);
        let lemmas = q.generate_lemmas(&mut euf, &BTreeMap::new());
        assert_eq!(lemmas.len(), q.ground_terms.len());
        assert!(lemmas.contains(&implies(&all, p(iv("a")))));
    }

    #[test]
    fn model_based_instance_only_when_the_model_falsifies_the_body() {
        let all = forall_x(eq(iv("x"), Expr::Int(3)));
        // x = 4 falsifies the body: the instance at 4 is produced.
        let mut q = QuantifierSolver::new();
        q.assert(&all);
        let lemmas = q.generate_lemmas(&mut EufSolver::new(), &int_model("x", 4));
        assert_eq!(lemmas, vec![implies(&all, eq(Expr::Int(4), Expr::Int(3)))]);
        // x = 3 satisfies it: nothing to add.
        let mut q = QuantifierSolver::new();
        q.assert(&all);
        let lemmas = q.generate_lemmas(&mut EufSolver::new(), &int_model("x", 3));
        assert!(lemmas.is_empty(), "{lemmas:?}");
        // evaluate_quantifier directly.
        assert!(!q.evaluate_quantifier(&all, &int_model("x", 4)));
        assert!(q.evaluate_quantifier(&all, &int_model("x", 3)));
        // Undecidable under the model, and non-universals, count as holding.
        assert!(q.evaluate_quantifier(&all, &BTreeMap::new()));
        assert!(q.evaluate_quantifier(&Expr::Bool(false), &BTreeMap::new()));
    }

    #[test]
    fn evaluation_of_ground_expressions() {
        let q = QuantifierSolver::new();
        let mut m = int_model("n", 5);
        m.insert("p".to_string(), ModelValue::Bool(true));
        m.insert("g".to_string(), ModelValue::Int(BigInt::from(9)));
        macro_rules! chk {
            ($a:expr, $b:expr) => {
                assert_eq!(format!("{:?}", $a), format!("{:?}", $b))
            };
        }
        let ev = |e: &Expr| q.evaluate_expr(e, &m);
        let t = Some(ModelValue::Bool(true));
        let fl = Some(ModelValue::Bool(false));
        chk!(ev(&iv("n")), Some(ModelValue::Int(BigInt::from(5))));
        chk!(ev(&iv("missing")), None::<ModelValue>);
        chk!(ev(&Expr::Bool(true)), t);
        chk!(ev(&Expr::Int(-7)), Some(ModelValue::Int(BigInt::from(-7))));
        chk!(
            ev(&Expr::Real(15, 1)),
            Some(ModelValue::Real(BigRational::new(
                BigInt::from(3),
                BigInt::from(2)
            )))
        );
        chk!(ev(&Expr::And(vec![Expr::Bool(true), Expr::Bool(true)])), t);
        chk!(
            ev(&Expr::And(vec![Expr::Bool(true), Expr::Bool(false)])),
            fl
        );
        chk!(ev(&Expr::And(vec![Expr::Bool(false), iv("missing")])), fl);
        chk!(
            ev(&Expr::And(vec![Expr::Bool(true), iv("missing")])),
            None::<ModelValue>
        );
        chk!(ev(&Expr::Not(b(Expr::Bool(true)))), fl);
        chk!(ev(&Expr::Not(b(Expr::Bool(false)))), t);
        chk!(ev(&Expr::Not(b(iv("missing")))), None::<ModelValue>);
        chk!(ev(&eq(iv("n"), Expr::Int(5))), t);
        chk!(ev(&eq(iv("n"), Expr::Int(6))), fl);
        chk!(ev(&eq(Expr::Real(5, 1), Expr::Real(1, 1))), fl);
        chk!(ev(&eq(Expr::Real(5, 1), Expr::Real(50, 2))), t);
        chk!(ev(&eq(iv("n"), Expr::Real(5, 0))), None::<ModelValue>);
        chk!(
            ev(&Expr::App("g".to_string(), vec![])),
            Some(ModelValue::Int(BigInt::from(9)))
        );
        chk!(
            ev(&Expr::Ge(b(iv("n")), b(Expr::Int(1)))),
            None::<ModelValue>
        );
    }

    #[test]
    fn model_values_become_literals() {
        let q = QuantifierSolver::new();
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Bool(true), &Type::Bool),
            Some(Expr::Bool(true))
        );
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Bool(false), &Type::Int),
            Some(Expr::Bool(false))
        );
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Int(BigInt::from(-4)), &Type::Int),
            Some(Expr::Int(-4))
        );
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Int(BigInt::from(1u8) << 100), &Type::Int),
            None
        );
        let whole = BigRational::from_integer(BigInt::from(6));
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Real(whole), &Type::Real),
            Some(Expr::Real(6, 0))
        );
        let frac = BigRational::new(BigInt::from(1), BigInt::from(2));
        assert_eq!(
            q.model_val_to_expr(&ModelValue::Real(frac), &Type::Real),
            None
        );
    }
}
