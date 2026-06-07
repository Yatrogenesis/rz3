use crate::ast::{Expr, Type, ModelValue};
use crate::theory::TheorySolver;
use crate::theory::euf::{EufSolver, Node};
use std::collections::{BTreeMap, BTreeSet};

pub struct QuantifierSolver {
    quantifiers: Vec<Expr>,
    ground_terms: BTreeSet<Expr>,
    instantiations: BTreeSet<Expr>,
    pattern_index: BTreeMap<String, Vec<usize>>,
}

impl Default for QuantifierSolver { fn default() -> Self { Self::new() } }

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
                for arg in args { self.collect_ground_terms(arg, euf); }
            }
            Expr::Select(a, i) => {
                if let Some(id) = euf.get_id_public(expr) {
                    self.pattern_index.entry("select".to_string()).or_default().push(id);
                }
                self.collect_ground_terms(a, euf);
                self.collect_ground_terms(i, euf);
            }
            _ => {}
        }
    }

    pub fn generate_lemmas(&mut self, euf: &mut EufSolver, model: &BTreeMap<String, ModelValue>) -> Vec<Expr> {
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
                            let lemma = Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                            if self.instantiations.insert(lemma.clone()) { lemmas.push(lemma); }
                        }
                    }
                }
                
                // MBQI: Instanciación basada en modelo si es falso
                if !self.evaluate_quantifier(q_expr, model) {
                    let mut sub = BTreeMap::new();
                    for (name, ty) in vars {
                        if let Some(val) = model.get(name) {
                            sub.insert(name.clone(), self.model_val_to_expr(val, ty));
                        }
                    }
                    let instantiated = body.substitute(&sub);
                    let lemma = Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                    if self.instantiations.insert(lemma.clone()) { lemmas.push(lemma); }
                }

                // E-matching
                let patterns = self.infer_patterns(body, vars);
                for pattern in patterns {
                    let mut substitutions = Vec::new();
                    self.match_pattern(&pattern, vars, euf, &mut BTreeMap::new(), &mut substitutions);
                    for sub in substitutions {
                        let instantiated = body.substitute(&sub);
                        let lemma = Expr::Implies(Box::new(q_expr.clone()), Box::new(instantiated));
                        if self.instantiations.insert(lemma.clone()) { lemmas.push(lemma); }
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
                        sub.insert(name.clone(), self.model_val_to_expr(val, ty));
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

    fn evaluate_expr(&self, expr: &Expr, model: &BTreeMap<String, ModelValue>) -> Option<ModelValue> {
        match expr {
            Expr::Var(name, _) => model.get(name).cloned(),
            Expr::Bool(b) => Some(ModelValue::Bool(*b)),
            Expr::Int(i) => Some(ModelValue::Int(*i)),
            Expr::Real(i, s) => Some(ModelValue::Real(*i as f64 / 10i64.pow(*s) as f64)),
            Expr::And(args) => {
                let mut res = true;
                for arg in args {
                    if let Some(ModelValue::Bool(b)) = self.evaluate_expr(arg, model) {
                        if !b { res = false; break; }
                    } else { return None; }
                }
                Some(ModelValue::Bool(res))
            }
            Expr::Not(inner) => {
                if let Some(ModelValue::Bool(b)) = self.evaluate_expr(inner, model) {
                    Some(ModelValue::Bool(!b))
                } else { None }
            }
            Expr::Eq(a, b) => {
                let ea = self.evaluate_expr(a, model);
                let eb = self.evaluate_expr(b, model);
                match (ea, eb) {
                    (Some(ModelValue::Int(va)), Some(ModelValue::Int(vb))) => Some(ModelValue::Bool(va == vb)),
                    (Some(ModelValue::Real(va)), Some(ModelValue::Real(vb))) => Some(ModelValue::Bool((va - vb).abs() < 1e-6)),
                    _ => None
                }
            }
            Expr::App(name, _args) => model.get(name).cloned(),
            _ => None,
        }
    }

    fn model_val_to_expr(&self, val: &ModelValue, ty: &Type) -> Expr {
        match (val, ty) {
            (ModelValue::Bool(b), _) => Expr::Bool(*b),
            (ModelValue::Int(i), _) => Expr::Int(*i),
            (ModelValue::Real(r), _) => Expr::Real(*r as i64, 0),
            _ => Expr::Bool(true),
        }
    }

    fn infer_patterns(&self, body: &Expr, vars: &[(String, Type)]) -> Vec<Expr> {
        let mut patterns = Vec::new();
        self.collect_apps(body, vars, &mut patterns);
        if patterns.is_empty() { patterns.push(body.clone()); }
        patterns
    }

    fn collect_apps(&self, expr: &Expr, vars: &[(String, Type)], patterns: &mut Vec<Expr>) {
        match expr {
            Expr::App(_, _) | Expr::Select(_, _) 
                if vars.iter().any(|(vname, _)| self.uses_variable(expr, vname)) => {
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
                        && sub.len() == vars.len() {
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
                    let existing_id = ctx.euf.get_id_public(existing).unwrap();
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
        if p_args.is_empty() { return true; }
        let mut sub = current_sub.clone();
        if self.match_recursive(&p_args[0], t_args[0], &mut sub, ctx)
            && self.match_args(&p_args[1..], &t_args[1..], &mut sub, ctx) {
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
        if let Expr::ForAll(_, _) = expr { self.quantifiers.push(expr.clone()); }
    }
    fn check(&mut self) -> bool { true }
    fn explain(&self) -> Vec<Expr> { Vec::new() }
    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> { None }
}
