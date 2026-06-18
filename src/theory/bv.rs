use crate::ast::{Expr, Type};
use crate::sat::CdclSolver;
use std::collections::BTreeMap;

// REF: [Hadarean et al., 2014] DOI: 10.1007/978-3-319-08867-9_7

pub struct BitBlaster<'a> {
    sat_solver: &'a mut CdclSolver,
    bv_vars: &'a mut BTreeMap<(String, usize), i32>,
    expr_to_bits: &'a mut BTreeMap<Expr, Vec<i32>>,
    next_var: &'a mut i32,
}

impl<'a> BitBlaster<'a> {
    pub fn new(
        sat_solver: &'a mut CdclSolver,
        bv_vars: &'a mut BTreeMap<(String, usize), i32>,
        expr_to_bits: &'a mut BTreeMap<Expr, Vec<i32>>,
        next_var: &'a mut i32,
    ) -> Self {
        Self {
            sat_solver,
            bv_vars,
            expr_to_bits,
            next_var,
        }
    }

    fn new_var(&mut self) -> i32 {
        let v = *self.next_var;
        *self.next_var += 1;
        self.sat_solver.ok = true; // Placeholder para asegurar que el motor SAT esté activo
        v
    }

    pub fn bit_blast(&mut self, expr: &Expr) -> Vec<i32> {
        if let Some(bits) = self.expr_to_bits.get(expr) {
            return bits.clone();
        }

        let simplified = self.word_level_simplify(expr);
        let bits = match simplified {
            Expr::BvConst(val, width) => {
                let mut b = Vec::new();
                for i in 0..width {
                    let v = self.new_var();
                    if (val >> i) & 1 == 1 {
                        self.sat_solver.add_clause(vec![v]);
                    } else {
                        self.sat_solver.add_clause(vec![-v]);
                    }
                    b.push(v);
                }
                b
            }
            Expr::Var(name, Type::BitVec(width)) => {
                let mut b = Vec::new();
                for i in 0..width {
                    let v = *self.bv_vars.entry((name.clone(), i)).or_insert_with(|| {
                        let nv = *self.next_var;
                        *self.next_var += 1;
                        nv
                    });
                    b.push(v);
                }
                b
            }
            Expr::BvAnd(a, b) => {
                let bits_a = self.bit_blast(&a);
                let bits_b = self.bit_blast(&b);
                let mut res = Vec::new();
                for (la, lb) in bits_a.into_iter().zip(bits_b) {
                    let lr = self.new_var();
                    // lr <=> (la AND lb)
                    // (!la | !lb | lr), (la | !lr), (lb | !lr)
                    self.sat_solver.add_clause(vec![-la, -lb, lr]);
                    self.sat_solver.add_clause(vec![la, -lr]);
                    self.sat_solver.add_clause(vec![lb, -lr]);
                    res.push(lr);
                }
                res
            }
            Expr::BvAdd(a, b) => {
                let bits_a = self.bit_blast(&a);
                let bits_b = self.bit_blast(&b);
                let mut res = Vec::new();
                let mut carry = self.new_var();
                self.sat_solver.add_clause(vec![-carry]);
                for (la, lb) in bits_a.into_iter().zip(bits_b) {
                    let sum = self.new_var();
                    let next_carry = self.new_var();
                    self.add_xor3(sum, la, lb, carry);
                    self.add_maj3(next_carry, la, lb, carry);
                    res.push(sum);
                    carry = next_carry;
                }
                res
            }
            _ => vec![],
        };
        self.expr_to_bits.insert(expr.clone(), bits.clone());
        bits
    }

    fn word_level_simplify(&self, expr: &Expr) -> Expr {
        match expr {
            Expr::BvAnd(a, b) => {
                if let Expr::BvConst(0, w) = &**a {
                    return Expr::BvConst(0, *w);
                }
                if let Expr::BvConst(0, w) = &**b {
                    return Expr::BvConst(0, *w);
                }
            }
            Expr::BvAdd(a, b) => {
                if let Expr::BvConst(0, _) = &**a {
                    return *b.clone();
                }
                if let Expr::BvConst(0, _) = &**b {
                    return *a.clone();
                }
            }
            _ => {}
        }
        expr.clone()
    }

    fn add_xor3(&mut self, res: i32, a: i32, b: i32, c: i32) {
        self.sat_solver.add_clause(vec![a, b, c, -res]);
        self.sat_solver.add_clause(vec![a, b, -c, res]);
        self.sat_solver.add_clause(vec![a, -b, c, res]);
        self.sat_solver.add_clause(vec![a, -b, -c, -res]);
        self.sat_solver.add_clause(vec![-a, b, c, res]);
        self.sat_solver.add_clause(vec![-a, b, -c, -res]);
        self.sat_solver.add_clause(vec![-a, -b, c, -res]);
        self.sat_solver.add_clause(vec![-a, -b, -c, res]);
    }

    fn add_maj3(&mut self, res: i32, a: i32, b: i32, c: i32) {
        self.sat_solver.add_clause(vec![-a, -b, res]);
        self.sat_solver.add_clause(vec![-b, -c, res]);
        self.sat_solver.add_clause(vec![-a, -c, res]);
        self.sat_solver.add_clause(vec![a, b, -res]);
        self.sat_solver.add_clause(vec![b, c, -res]);
        self.sat_solver.add_clause(vec![a, c, -res]);
    }
}
