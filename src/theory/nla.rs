use crate::ast::{Expr, ModelValue};
use crate::theory::TheorySolver;
use std::collections::BTreeMap;
use num_bigint::BigInt;

// REF: [Collins, 1975] DOI: 10.1007/3-540-07407-7_17
// REF: [Sturm, 1835] Aislamiento de raíces reales univariadas.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultivariatePolynomial {
    pub terms: BTreeMap<Vec<u32>, BigInt>,
}

impl Default for MultivariatePolynomial { fn default() -> Self { Self::new() } }

impl MultivariatePolynomial {
    pub fn new() -> Self { Self { terms: BTreeMap::new() } }

    pub fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (exps, coeff) in &other.terms {
            *result.terms.entry(exps.clone()).or_insert(BigInt::from(0)) += coeff;
        }
        result.cleanup();
        result
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut result = Self::new();
        for (exps1, coeff1) in &self.terms {
            for (exps2, coeff2) in &other.terms {
                let mut new_exps = exps1.clone();
                let max_len = exps1.len().max(exps2.len());
                new_exps.resize(max_len, 0);
                for (i, &exp) in exps2.iter().enumerate() { new_exps[i] += exp; }
                *result.terms.entry(new_exps).or_insert(BigInt::from(0)) += coeff1 * coeff2;
            }
        }
        result.cleanup();
        result
    }

    pub fn degree(&self, var_idx: usize) -> u32 {
        self.terms.keys()
            .map(|exps| if var_idx < exps.len() { exps[var_idx] } else { 0 })
            .max()
            .unwrap_or(0)
    }

    pub fn leading_coefficient(&self, var_idx: usize) -> Self {
        let deg = self.degree(var_idx);
        let mut result = Self::new();
        for (exps, coeff) in &self.terms {
            let d = if var_idx < exps.len() { exps[var_idx] } else { 0 };
            if d == deg {
                let mut new_exps = exps.clone();
                if var_idx < new_exps.len() { new_exps[var_idx] = 0; }
                *result.terms.entry(new_exps).or_insert(BigInt::from(0)) += coeff;
            }
        }
        result.cleanup();
        result
    }

    pub fn lift(&self, var_idx: usize, power: u32) -> Self {
        let mut result = Self::new();
        for (exps, coeff) in &self.terms {
            let mut new_exps = exps.clone();
            if var_idx >= new_exps.len() { new_exps.resize(var_idx + 1, 0); }
            new_exps[var_idx] += power;
            result.terms.insert(new_exps, coeff.clone());
        }
        result
    }

    pub fn pseudo_remainder(&self, other: &Self, var_idx: usize) -> Self {
        let deg_p = self.degree(var_idx);
        let deg_q = other.degree(var_idx);
        if deg_p < deg_q { return self.clone(); }
        let lc_q = other.leading_coefficient(var_idx);
        let mut r = self.clone();
        let k = deg_p - deg_q + 1;
        for _ in 0..k {
            let deg_r = r.degree(var_idx);
            if deg_r < deg_q { break; }
            let lc_r = r.leading_coefficient(var_idx);
            let term = lc_r.lift(var_idx, deg_r - deg_q);
            let mut next_r = r.mul(&lc_q);
            let sub = term.mul(other);
            for (exps, coeff) in sub.terms {
                *next_r.terms.entry(exps).or_insert(BigInt::from(0)) -= coeff;
            }
            next_r.cleanup();
            r = next_r;
        }
        r
    }

    pub fn resultant(&self, other: &Self, var_idx: usize) -> Self {
        let mut f = self.clone();
        let mut g = other.clone();
        if f.degree(var_idx) < g.degree(var_idx) { std::mem::swap(&mut f, &mut g); }
        if g.degree(var_idx) == 0 { return g; }
        let mut r = f.pseudo_remainder(&g, var_idx);
        while r.degree(var_idx) > 0 {
            f = g; g = r;
            r = f.pseudo_remainder(&g, var_idx);
        }
        r
    }

    pub fn partial_derivative(&self, var_idx: usize) -> Self {
        let mut result = Self::new();
        for (exps, coeff) in &self.terms {
            if var_idx < exps.len() && exps[var_idx] > 0 {
                let mut new_exps = exps.clone();
                let exp = exps[var_idx];
                new_exps[var_idx] -= 1;
                *result.terms.entry(new_exps).or_insert(BigInt::from(0)) += coeff * BigInt::from(exp);
            }
        }
        result.cleanup();
        result
    }

    pub fn evaluate_univariate(&self, var_idx: usize, val: &BigInt) -> BigInt {
        let mut result = BigInt::from(0);
        for (exps, coeff) in &self.terms {
            let exp = if var_idx < exps.len() { exps[var_idx] } else { 0 };
            let mut term_val = coeff.clone();
            for _ in 0..exp { term_val *= val; }
            result += term_val;
        }
        result
    }

    fn cleanup(&mut self) {
        self.terms.retain(|_, v| v != &BigInt::from(0));
    }
}

pub struct NlaSolver {
    constraints: Vec<Expr>,
    var_map: BTreeMap<String, usize>,
    next_var_idx: usize,
}

impl Default for NlaSolver { fn default() -> Self { Self::new() } }

impl NlaSolver {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            var_map: BTreeMap::new(),
            next_var_idx: 0,
        }
    }

    pub fn reset(&mut self) {
        self.constraints.clear();
        self.var_map.clear();
        self.next_var_idx = 0;
    }

    fn get_var_idx(&mut self, name: &str) -> usize {
        *self.var_map.entry(name.to_string()).or_insert_with(|| {
            let idx = self.next_var_idx;
            self.next_var_idx += 1;
            idx
        })
    }

    pub fn expr_to_poly(&mut self, expr: &Expr) -> Option<MultivariatePolynomial> {
        match expr {
            Expr::Int(i) => {
                let mut p = MultivariatePolynomial::new();
                p.terms.insert(vec![], BigInt::from(*i));
                Some(p)
            }
            Expr::Var(name, _) => {
                let idx = self.get_var_idx(name);
                let mut p = MultivariatePolynomial::new();
                let mut exps = vec![0; idx + 1];
                exps[idx] = 1;
                p.terms.insert(exps, BigInt::from(1));
                Some(p)
            }
            Expr::Add(args) => {
                let mut res = MultivariatePolynomial::new();
                for arg in args { res = res.add(&self.expr_to_poly(arg)?); }
                Some(res)
            }
            Expr::Mul(args) => {
                let mut res = MultivariatePolynomial::new();
                res.terms.insert(vec![], BigInt::from(1));
                for arg in args { res = res.mul(&self.expr_to_poly(arg)?); }
                Some(res)
            }
            Expr::Sub(args) => {
                if args.is_empty() { return Some(MultivariatePolynomial::new()); }
                let mut res = self.expr_to_poly(&args[0])?;
                for arg in &args[1..] {
                    let mut neg = self.expr_to_poly(arg)?;
                    for v in neg.terms.values_mut() { *v *= -1; }
                    res = res.add(&neg);
                }
                Some(res)
            }
            _ => None,
        }
    }

    pub fn project(&mut self, polys: &[MultivariatePolynomial], var_idx: usize) -> Vec<MultivariatePolynomial> {
        let mut proj = Vec::new();
        for (i, p) in polys.iter().enumerate() {
            proj.push(p.leading_coefficient(var_idx));
            proj.push(p.partial_derivative(var_idx));
            for q in &polys[i+1..] { proj.push(p.resultant(q, var_idx)); }
        }
        proj.retain(|p| !p.terms.is_empty());
        proj
    }

    pub fn sturm_sequence(&self, poly: &MultivariatePolynomial, var_idx: usize) -> Vec<MultivariatePolynomial> {
        let mut seq = Vec::new();
        if poly.terms.is_empty() { return seq; }
        seq.push(poly.clone());
        seq.push(poly.partial_derivative(var_idx));
        while let Some(last) = seq.last() {
            if last.degree(var_idx) == 0 { break; }
            let p_prev = &seq[seq.len() - 2];
            let mut r = p_prev.pseudo_remainder(last, var_idx);
            for v in r.terms.values_mut() { *v *= -1; }
            r.cleanup();
            if r.terms.is_empty() { break; }
            seq.push(r);
        }
        seq
    }
}

impl TheorySolver for NlaSolver {
    fn assert(&mut self, expr: &Expr) { self.constraints.push(expr.clone()); }

    fn check(&mut self) -> bool {
        // ... (existing implementation)
        if self.constraints.is_empty() { return true; }

        let mut polys_with_op = Vec::new();
        for expr in self.constraints.clone() {
            match expr {
                Expr::Lt(a, b) => { if let Some(p) = self.expr_to_poly(&Expr::Sub(vec![*a, *b])) { polys_with_op.push((p, "lt")); } }
                Expr::Gt(a, b) => { if let Some(p) = self.expr_to_poly(&Expr::Sub(vec![*a, *b])) { polys_with_op.push((p, "gt")); } }
                Expr::Le(a, b) => { if let Some(p) = self.expr_to_poly(&Expr::Sub(vec![*a, *b])) { polys_with_op.push((p, "le")); } }
                Expr::Ge(a, b) => { if let Some(p) = self.expr_to_poly(&Expr::Sub(vec![*a, *b])) { polys_with_op.push((p, "ge")); } }
                Expr::Eq(a, b) => { if let Some(p) = self.expr_to_poly(&Expr::Sub(vec![*a, *b])) { polys_with_op.push((p, "eq")); } }
                _ => {}
            }
        }
        for (p, op) in polys_with_op {
            let mut all_even = true;
            let mut all_coeffs_non_neg = true;
            let mut has_const_pos = false;
            for (exps, coeff) in &p.terms {
                if exps.iter().any(|&e| e % 2 != 0) { all_even = false; }
                if coeff < &BigInt::from(0) { all_coeffs_non_neg = false; }
                if exps.iter().all(|&e| e == 0) && coeff > &BigInt::from(0) { has_const_pos = true; }
            }
            if all_even && all_coeffs_non_neg && has_const_pos && op == "lt" { return false; }
            if all_even && all_coeffs_non_neg && has_const_pos && op == "le" && p.terms.values().all(|v| v >= &BigInt::from(0)) { return false; }
        }
        true
    }

    fn explain(&self) -> Vec<Expr> { self.constraints.clone() }

    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> {
        None
    }
}

