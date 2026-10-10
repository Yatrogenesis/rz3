//! Ring normalisation of bit-vector terms over Z/2^w.
//!
//! `bvadd`, `bvsub`, `bvneg`, `bvmul` and constants are interpreted as polynomial
//! arithmetic in the commutative ring Z/2^w; every other sub-term is an opaque
//! atom (compared structurally). An equality whose two sides have the same
//! normal form holds in every model, so it is rewritten to `true`. The rewrite
//! uses only ring identities, hence it never changes the meaning of the formula.
//! The normal form is not unique for Z/2^w polynomials (e.g. `2^(w-1)*x*(x+1) = 0`),
//! so the pass is sound but deliberately incomplete.
use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use crate::ast::{Expr, Type};
use crate::tactic::Tactic;

/// Above this many monomials in a product the term is kept as an opaque atom.
const MAX_PRODUCT_TERMS: usize = 200_000;

/// Monomial (sorted multiset of atoms) -> non-zero coefficient in [1, 2^w).
type Poly = BTreeMap<Vec<Expr>, BigUint>;

pub struct BvRing;

impl Tactic for BvRing {
    fn apply(&self, expr: Expr) -> Expr {
        Self::rewrite(&expr)
    }
}

impl BvRing {
    /// Rewrite every `(= a b)` over bit-vectors whose sides are ring-equal to `true`.
    pub fn rewrite(e: &Expr) -> Expr {
        let rebuilt = e.map_children(&mut |c| Self::rewrite(c));
        if let Expr::Eq(a, b) = &rebuilt {
            if let (Type::BitVec(wa), Type::BitVec(wb)) = (a.get_type(), b.get_type()) {
                if wa == wb && wa > 0 && Self::normal_form(a, wa) == Self::normal_form(b, wa) {
                    return Expr::Bool(true);
                }
            }
        }
        rebuilt
    }

    /// Canonical polynomial of `e` read as a width-`w` term.
    pub fn normal_form(e: &Expr, w: usize) -> Poly {
        let modulus = BigUint::one() << w;
        Self::poly(e, w, &modulus)
    }

    fn atom(e: &Expr) -> Poly {
        let mut p = Poly::new();
        p.insert(vec![e.clone()], BigUint::one());
        p
    }

    fn add(a: Poly, b: Poly, m: &BigUint) -> Poly {
        let mut out = a;
        for (mono, c) in b {
            let v = match out.remove(&mono) {
                Some(old) => (old + c) % m,
                None => c % m,
            };
            if !v.is_zero() {
                out.insert(mono, v);
            }
        }
        out
    }

    fn neg(a: Poly, m: &BigUint) -> Poly {
        a.into_iter()
            .map(|(mono, c)| (mono, m - c))
            .filter(|(_, c)| !c.is_zero())
            .collect()
    }

    fn mul(a: &Poly, b: &Poly, m: &BigUint) -> Option<Poly> {
        if a.len().saturating_mul(b.len()) > MAX_PRODUCT_TERMS {
            return None;
        }
        let mut out = Poly::new();
        for (ma, ca) in a {
            for (mb, cb) in b {
                let mut mono = ma.clone();
                mono.extend(mb.iter().cloned());
                mono.sort_unstable();
                let c = (ca * cb) % m;
                if c.is_zero() {
                    continue;
                }
                let v = match out.remove(&mono) {
                    Some(old) => (old + c) % m,
                    None => c,
                };
                if !v.is_zero() {
                    out.insert(mono, v);
                }
            }
        }
        Some(out)
    }

    fn poly(e: &Expr, w: usize, m: &BigUint) -> Poly {
        match e {
            Expr::BvConst(v, cw) if *cw == w => {
                let c = v % m;
                let mut p = Poly::new();
                if !c.is_zero() {
                    p.insert(Vec::new(), c);
                }
                p
            }
            Expr::BvAdd(a, b) => Self::add(Self::poly(a, w, m), Self::poly(b, w, m), m),
            Expr::BvSub(a, b) => {
                Self::add(Self::poly(a, w, m), Self::neg(Self::poly(b, w, m), m), m)
            }
            Expr::BvNeg(a) => Self::neg(Self::poly(a, w, m), m),
            Expr::BvMul(a, b) => {
                let (pa, pb) = (Self::poly(a, w, m), Self::poly(b, w, m));
                Self::mul(&pa, &pb, m).unwrap_or_else(|| Self::atom(e))
            }
            _ => Self::atom(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(name: &str, w: usize) -> Expr {
        Expr::Var(name.to_string(), Type::BitVec(w))
    }
    fn c(n: u64, w: usize) -> Expr {
        Expr::BvConst(BigUint::from(n), w)
    }
    fn b(e: Expr) -> Box<Expr> {
        Box::new(e)
    }
    fn eq(a: Expr, z: Expr) -> Expr {
        Expr::Eq(b(a), b(z))
    }

    #[test]
    fn distributivity_is_decided_by_normal_forms_not_by_the_sat_solver() {
        let (x, y, z) = (v("x", 8), v("y", 8), v("z", 8));
        let lhs = Expr::BvMul(b(x.clone()), b(Expr::BvAdd(b(y.clone()), b(z.clone()))));
        let rhs = Expr::BvAdd(
            b(Expr::BvMul(b(x.clone()), b(y.clone()))),
            b(Expr::BvMul(b(x), b(z))),
        );
        assert_eq!(BvRing::rewrite(&eq(lhs, rhs)), Expr::Bool(true));
    }

    #[test]
    fn non_identities_are_left_alone() {
        let (x, y, z) = (v("x", 8), v("y", 8), v("z", 8));
        let e = eq(
            Expr::BvMul(b(x.clone()), b(y.clone())),
            Expr::BvMul(b(x.clone()), b(z)),
        );
        assert_eq!(BvRing::rewrite(&e), e);
        let e = eq(
            Expr::BvAdd(b(x.clone()), b(y.clone())),
            Expr::BvMul(b(x), b(y)),
        );
        assert_eq!(BvRing::rewrite(&e), e);
    }

    #[test]
    fn coefficients_wrap_modulo_two_to_the_width() {
        // 16 * 16 = 256 = 0 (mod 256); 200 + 100 = 44; 3 - 5 = 254; -(1) = 255.
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvMul(b(c(16, 8)), b(c(16, 8))), c(0, 8))),
            Expr::Bool(true)
        );
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvAdd(b(c(200, 8)), b(c(100, 8))), c(44, 8))),
            Expr::Bool(true)
        );
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvSub(b(c(3, 8)), b(c(5, 8))), c(254, 8))),
            Expr::Bool(true)
        );
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvNeg(b(c(1, 8))), c(255, 8))),
            Expr::Bool(true)
        );
        // 16 * 17 = 272 = 16 (mod 256), not 0
        let e = eq(Expr::BvMul(b(c(16, 8)), b(c(17, 8))), c(0, 8));
        assert_eq!(BvRing::rewrite(&e), e);
    }

    #[test]
    fn x_minus_x_and_double_negation_cancel() {
        let x = v("x", 16);
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvSub(b(x.clone()), b(x.clone())), c(0, 16))),
            Expr::Bool(true)
        );
        assert_eq!(
            BvRing::rewrite(&eq(Expr::BvNeg(b(Expr::BvNeg(b(x.clone())))), x)),
            Expr::Bool(true)
        );
    }

    #[test]
    fn a_constant_of_another_width_is_an_atom_not_a_number() {
        // Ill-typed on purpose: a 4-bit constant read as an 8-bit term must not be reduced.
        let p = BvRing::normal_form(&c(5, 4), 8);
        assert_eq!(p.len(), 1);
        assert!(p.keys().all(|mono| mono.len() == 1));
    }

    #[test]
    fn opaque_operators_are_atoms_compared_structurally() {
        let (x, y) = (v("x", 8), v("y", 8));
        let a = Expr::BvAnd(b(x.clone()), b(y.clone()));
        let e = eq(
            Expr::BvAdd(b(a.clone()), b(a.clone())),
            Expr::BvMul(b(c(2, 8)), b(a)),
        );
        assert_eq!(BvRing::rewrite(&e), Expr::Bool(true));
        let e = eq(
            Expr::BvAnd(b(x.clone()), b(y.clone())),
            Expr::BvAnd(b(y), b(x)),
        );
        assert_eq!(BvRing::rewrite(&e), e, "bvand is an atom: not reordered");
    }

    fn sum_of(prefix: &str, n: usize) -> Expr {
        let mut acc = v(&format!("{prefix}0"), 16);
        for k in 1..n {
            acc = Expr::BvAdd(b(acc), b(v(&format!("{prefix}{k}"), 16)));
        }
        acc
    }

    #[test]
    fn products_up_to_the_cap_expand_and_larger_ones_stay_atoms() {
        // 400 x 500 = 200,000 monomials is exactly the cap: still expanded.
        let at_cap = Expr::BvMul(b(sum_of("x", 400)), b(sum_of("y", 500)));
        assert_eq!(BvRing::normal_form(&at_cap, 16).len(), 200_000);
        // 400 x 501 = 200,400 exceeds it: the whole product is one opaque atom.
        let over = Expr::BvMul(b(sum_of("x", 400)), b(sum_of("y", 501)));
        assert_eq!(BvRing::normal_form(&over, 16).len(), 1);
    }
}
