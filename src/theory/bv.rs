use crate::ast::{Expr, Type};
use crate::sat::CdclSolver;
use std::collections::BTreeMap;

// REF: [Hadarean et al., 2014] DOI: 10.1007/978-3-319-08867-9_7

/// Hard cap on bit-vector width `bit_blast` will expand. Width is an
/// unconstrained `usize` on `Expr::BvConst`/`Type::BitVec` — with no bound,
/// a single declared/constant bit-vector (e.g. from untrusted SMT-LIB input)
/// can drive the `for i in 0..width` loops below to allocate one SAT
/// variable + clause per bit with no upper limit, which is an OOM/DoS vector
/// in memory-constrained targets (wasm32 in particular — see the RZ3-5
/// soundness/hardening audit). 4096 bits comfortably covers realistic use
/// (SHA-256 chains, RSA moduli well beyond typical register widths) while
/// keeping a single term's expansion bounded.
pub const MAX_BV_WIDTH: usize = 4096;

/// Bit-blaster for the QF_BV operators of [`Expr`].
///
/// Bits are least-significant first. Anything this encoder cannot translate
/// faithfully sets [`BitBlaster::unsupported`] instead of producing an
/// unconstrained or empty vector: callers must check it and decline to report
/// satisfiable (an unconstrained term would be a silent soundness hole).
pub struct BitBlaster<'a> {
    sat_solver: &'a mut CdclSolver,
    bv_vars: &'a mut BTreeMap<(String, usize), i32>,
    expr_to_bits: &'a mut BTreeMap<Expr, Vec<i32>>,
    next_var: &'a mut i32,
    /// An operator, operand mismatch or term shape was not encoded.
    pub unsupported: bool,
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
            unsupported: false,
        }
    }

    fn new_var(&mut self) -> i32 {
        let v = *self.next_var;
        *self.next_var += 1;
        v
    }

    fn clause(&mut self, lits: Vec<i32>) {
        let _ = self.sat_solver.add_clause(lits);
    }

    fn constant(&mut self, value: bool) -> i32 {
        let v = self.new_var();
        self.clause(vec![if value { v } else { -v }]);
        v
    }

    fn and2(&mut self, a: i32, b: i32) -> i32 {
        let r = self.new_var();
        self.clause(vec![-a, -b, r]);
        self.clause(vec![a, -r]);
        self.clause(vec![b, -r]);
        r
    }

    fn or2(&mut self, a: i32, b: i32) -> i32 {
        -self.and2(-a, -b)
    }

    fn xor2(&mut self, a: i32, b: i32) -> i32 {
        let r = self.new_var();
        self.clause(vec![-a, -b, -r]);
        self.clause(vec![a, b, -r]);
        self.clause(vec![a, -b, r]);
        self.clause(vec![-a, b, r]);
        r
    }

    /// `s ? a : b`
    fn mux(&mut self, s: i32, a: i32, b: i32) -> i32 {
        let r = self.new_var();
        self.clause(vec![-s, -a, r]);
        self.clause(vec![-s, a, -r]);
        self.clause(vec![s, -b, r]);
        self.clause(vec![s, b, -r]);
        r
    }

    fn add_xor3(&mut self, res: i32, a: i32, b: i32, c: i32) {
        self.clause(vec![a, b, c, -res]);
        self.clause(vec![a, b, -c, res]);
        self.clause(vec![a, -b, c, res]);
        self.clause(vec![a, -b, -c, -res]);
        self.clause(vec![-a, b, c, res]);
        self.clause(vec![-a, b, -c, -res]);
        self.clause(vec![-a, -b, c, -res]);
        self.clause(vec![-a, -b, -c, res]);
    }

    fn add_maj3(&mut self, res: i32, a: i32, b: i32, c: i32) {
        self.clause(vec![-a, -b, res]);
        self.clause(vec![-b, -c, res]);
        self.clause(vec![-a, -c, res]);
        self.clause(vec![a, b, -res]);
        self.clause(vec![b, c, -res]);
        self.clause(vec![a, c, -res]);
    }

    /// Ripple-carry sum of equal-width vectors with the given carry-in literal.
    fn adder(&mut self, a: &[i32], b: &[i32], carry_in: i32) -> Vec<i32> {
        let mut carry = carry_in;
        let mut out = Vec::with_capacity(a.len());
        for (&la, &lb) in a.iter().zip(b) {
            let sum = self.new_var();
            let next = self.new_var();
            self.add_xor3(sum, la, lb, carry);
            self.add_maj3(next, la, lb, carry);
            out.push(sum);
            carry = next;
        }
        out
    }

    /// Literal that is true iff `a < b` (unsigned).
    fn ult(&mut self, a: &[i32], b: &[i32]) -> i32 {
        let mut lt = self.constant(false);
        for (&la, &lb) in a.iter().zip(b) {
            // lt' = (!a & b) | ((a <-> b) & lt)
            let strictly = self.and2(-la, lb);
            let differ = self.xor2(la, lb);
            let keep = self.and2(-differ, lt);
            lt = self.or2(strictly, keep);
        }
        lt
    }

    /// Literal that is true iff the two vectors are equal.
    fn equal(&mut self, a: &[i32], b: &[i32]) -> i32 {
        let mut all = self.constant(true);
        for (&la, &lb) in a.iter().zip(b) {
            let differ = self.xor2(la, lb);
            all = self.and2(all, -differ);
        }
        all
    }

    fn same_width(&mut self, a: &[i32], b: &[i32]) -> bool {
        if a.is_empty() || a.len() != b.len() {
            self.unsupported = true;
            false
        } else {
            true
        }
    }

    /// Shift by a variable amount. `kind`: 0 = left, 1 = logical right, 2 = arithmetic right.
    fn shifter(&mut self, value: &[i32], amount: &[i32], kind: u8) -> Vec<i32> {
        let w = value.len();
        let zero = self.constant(false);
        let fill = if kind == 2 { value[w - 1] } else { zero };
        let mut cur = value.to_vec();
        let mut stage = 0usize;
        while (1usize << stage) < w && stage < amount.len() {
            let by = 1usize << stage;
            let sel = amount[stage];
            let mut next = Vec::with_capacity(w);
            for i in 0..w {
                let shifted = if kind == 0 {
                    if i >= by {
                        cur[i - by]
                    } else {
                        zero
                    }
                } else if i + by < w {
                    cur[i + by]
                } else {
                    fill
                };
                next.push(self.mux(sel, shifted, cur[i]));
            }
            cur = next;
            stage += 1;
        }
        // Any amount >= w yields all-zero (or all-sign for arithmetic right shift).
        let width_const: Vec<i32> = (0..amount.len())
            .map(|i| {
                let bit = i < usize::BITS as usize && (w >> i) & 1 == 1;
                self.constant(bit)
            })
            .collect();
        let in_range = self.ult(amount, &width_const);
        cur.iter()
            .map(|&bit| self.mux(in_range, bit, fill))
            .collect()
    }

    pub fn bit_blast(&mut self, expr: &Expr) -> Vec<i32> {
        if let Some(bits) = self.expr_to_bits.get(expr) {
            return bits.clone();
        }
        let bits = self.encode(expr);
        if bits.is_empty() {
            self.unsupported = true;
        }
        self.expr_to_bits.insert(expr.clone(), bits.clone());
        bits
    }

    fn encode(&mut self, expr: &Expr) -> Vec<i32> {
        match expr {
            Expr::BvConst(val, width) => {
                assert!(
                    *width <= MAX_BV_WIDTH,
                    "BvConst width {width} exceeds MAX_BV_WIDTH ({MAX_BV_WIDTH}) — refusing to \
                     bit-blast (RZ3-5: unbounded expansion is an OOM/DoS vector, not a silently \
                     truncated result)"
                );
                (0..*width)
                    .map(|i| self.constant(i < 64 && (val >> i) & 1 == 1))
                    .collect()
            }
            Expr::Var(name, Type::BitVec(width)) => {
                assert!(
                    *width <= MAX_BV_WIDTH,
                    "BitVec width {width} for '{name}' exceeds MAX_BV_WIDTH ({MAX_BV_WIDTH}) — \
                     refusing to bit-blast (RZ3-5: unbounded expansion is an OOM/DoS vector, not \
                     a silently truncated result)"
                );
                (0..*width)
                    .map(|i| {
                        if let Some(&v) = self.bv_vars.get(&(name.clone(), i)) {
                            v
                        } else {
                            let v = *self.next_var;
                            *self.next_var += 1;
                            self.bv_vars.insert((name.clone(), i), v);
                            v
                        }
                    })
                    .collect()
            }
            Expr::BvNot(a) => {
                let bits = self.bit_blast(a);
                bits.into_iter().map(|b| -b).collect()
            }
            Expr::BvAnd(a, b) | Expr::BvOr(a, b) | Expr::BvXor(a, b) => {
                let (x, y) = (self.bit_blast(a), self.bit_blast(b));
                if !self.same_width(&x, &y) {
                    return vec![];
                }
                x.iter()
                    .zip(&y)
                    .map(|(&p, &q)| match expr {
                        Expr::BvAnd(_, _) => self.and2(p, q),
                        Expr::BvOr(_, _) => self.or2(p, q),
                        _ => self.xor2(p, q),
                    })
                    .collect()
            }
            Expr::BvAdd(a, b) => {
                let (x, y) = (self.bit_blast(a), self.bit_blast(b));
                if !self.same_width(&x, &y) {
                    return vec![];
                }
                let cin = self.constant(false);
                self.adder(&x, &y, cin)
            }
            Expr::BvSub(a, b) => {
                let (x, y) = (self.bit_blast(a), self.bit_blast(b));
                if !self.same_width(&x, &y) {
                    return vec![];
                }
                let not_y: Vec<i32> = y.iter().map(|&l| -l).collect();
                let cin = self.constant(true);
                self.adder(&x, &not_y, cin)
            }
            Expr::BvMul(a, b) => {
                let (x, y) = (self.bit_blast(a), self.bit_blast(b));
                if !self.same_width(&x, &y) {
                    return vec![];
                }
                let w = x.len();
                let zero = self.constant(false);
                let mut acc = vec![zero; w];
                for (i, &yi) in y.iter().enumerate() {
                    // (x << i) masked by y[i], truncated to w bits.
                    let partial: Vec<i32> = (0..w)
                        .map(|j| {
                            if j >= i {
                                self.and2(x[j - i], yi)
                            } else {
                                zero
                            }
                        })
                        .collect();
                    let cin = self.constant(false);
                    acc = self.adder(&acc, &partial, cin);
                }
                acc
            }
            Expr::BvShl(a, b) | Expr::BvLshr(a, b) | Expr::BvAshr(a, b) => {
                let (x, y) = (self.bit_blast(a), self.bit_blast(b));
                if !self.same_width(&x, &y) {
                    return vec![];
                }
                let kind = match expr {
                    Expr::BvShl(_, _) => 0,
                    Expr::BvLshr(_, _) => 1,
                    _ => 2,
                };
                self.shifter(&x, &y, kind)
            }
            Expr::BvExtract(h, l, a) => {
                let x = self.bit_blast(a);
                if *l > *h || *h >= x.len() {
                    self.unsupported = true;
                    return vec![];
                }
                x[*l..=*h].to_vec()
            }
            Expr::BvConcat(a, b) => {
                // `a` supplies the high bits, `b` the low bits.
                let (hi, lo) = (self.bit_blast(a), self.bit_blast(b));
                if hi.is_empty() || lo.is_empty() {
                    self.unsupported = true;
                    return vec![];
                }
                lo.into_iter().chain(hi).collect()
            }
            _ => {
                self.unsupported = true;
                vec![]
            }
        }
    }

    /// Literal for a bit-vector comparison or equality, or `None` (and
    /// `unsupported` set) if it cannot be encoded.
    pub fn predicate(&mut self, expr: &Expr) -> Option<i32> {
        let (a, b, kind) = match expr {
            Expr::Eq(a, b) => (a, b, 0u8),
            Expr::BvUlt(a, b) => (a, b, 1),
            Expr::BvUle(a, b) => (a, b, 2),
            Expr::BvSlt(a, b) => (a, b, 3),
            Expr::BvSle(a, b) => (a, b, 4),
            _ => {
                self.unsupported = true;
                return None;
            }
        };
        let (mut x, mut y) = (self.bit_blast(a), self.bit_blast(b));
        if !self.same_width(&x, &y) {
            return None;
        }
        if kind >= 3 {
            // Signed order = unsigned order with the sign bits flipped.
            let last = x.len() - 1;
            x[last] = -x[last];
            y[last] = -y[last];
        }
        Some(match kind {
            0 => self.equal(&x, &y),
            1 | 3 => self.ult(&x, &y),
            _ => -self.ult(&y, &x),
        })
    }
}
