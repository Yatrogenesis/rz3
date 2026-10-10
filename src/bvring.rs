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
