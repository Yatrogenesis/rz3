//! Exact rational numbers with a machine-integer fast path.
//!
//! `Q::S(n, d)` holds a reduced fraction with `d > 0` in `i64`. Every operation is done in
//! `i128` with explicit overflow checks; a result that no longer fits silently moves to
//! `Q::B`, an arbitrary-precision `BigRational`. Results are therefore always exact: the
//! fast path only changes speed, never the value.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};
use std::cmp::Ordering;

#[derive(Clone, Debug)]
pub enum Q {
    S(i64, i64),
    B(Box<BigRational>),
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Reduced `Q` from an `i128` fraction (`d != 0`).
fn from_i128(n: i128, d: i128) -> Q {
    debug_assert!(d != 0);
    let (mut n, mut d) = (n, d);
    if d < 0 {
        n = -n;
        d = -d;
    }
    let g = gcd_u128(n.unsigned_abs(), d.unsigned_abs()).max(1) as i128;
    let (n, d) = (n / g, d / g);
    match (i64::try_from(n), i64::try_from(d)) {
        (Ok(n), Ok(d)) => Q::S(n, d),
        _ => Q::B(Box::new(BigRational::new(BigInt::from(n), BigInt::from(d)))),
    }
}

impl Q {
    pub fn zero() -> Q {
        Q::S(0, 1)
    }

    pub fn one() -> Q {
        Q::S(1, 1)
    }

    pub fn from_i64(v: i64) -> Q {
        Q::S(v, 1)
    }

    pub fn from_big(r: &BigRational) -> Q {
        match (r.numer().to_i64(), r.denom().to_i64()) {
            (Some(n), Some(d)) => Q::S(n, d),
            _ => Q::B(Box::new(r.clone())),
        }
    }

    pub fn to_big(&self) -> BigRational {
        match self {
            Q::S(n, d) => BigRational::new(BigInt::from(*n), BigInt::from(*d)),
            Q::B(b) => (**b).clone(),
        }
    }

    fn normalise(r: BigRational) -> Q {
        Q::from_big(&r)
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Q::S(n, _) => *n == 0,
            Q::B(b) => b.is_zero(),
        }
    }

    pub fn signum(&self) -> i32 {
        match self {
            Q::S(n, _) => n.signum() as i32,
            Q::B(b) => {
                if b.is_zero() {
                    0
                } else if b.is_positive() {
                    1
                } else {
                    -1
                }
            }
        }
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Q::S(_, d) => *d == 1,
            Q::B(b) => b.is_integer(),
        }
    }

    pub fn neg(&self) -> Q {
        match self {
            Q::S(n, d) => match n.checked_neg() {
                Some(m) => Q::S(m, *d),
                None => Q::normalise(-self.to_big()),
            },
            Q::B(b) => Q::normalise(-(**b).clone()),
        }
    }

    pub fn abs(&self) -> Q {
        if self.signum() < 0 {
            self.neg()
        } else {
            self.clone()
        }
    }

    pub fn add(&self, o: &Q) -> Q {
        if let (Q::S(a, b), Q::S(c, d)) = (self, o) {
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            // a/b + c/d with b, d < 2^63: the products below stay inside i128.
            return from_i128(a * d + c * b, b * d);
        }
        Q::normalise(self.to_big() + o.to_big())
    }

    pub fn sub(&self, o: &Q) -> Q {
        if let (Q::S(a, b), Q::S(c, d)) = (self, o) {
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            return from_i128(a * d - c * b, b * d);
        }
        Q::normalise(self.to_big() - o.to_big())
    }

    pub fn mul(&self, o: &Q) -> Q {
        if let (Q::S(a, b), Q::S(c, d)) = (self, o) {
            return from_i128(*a as i128 * *c as i128, *b as i128 * *d as i128);
        }
        Q::normalise(self.to_big() * o.to_big())
    }

    /// Division; the divisor must be non-zero.
    pub fn div(&self, o: &Q) -> Q {
        debug_assert!(!o.is_zero());
        if let (Q::S(a, b), Q::S(c, d)) = (self, o) {
            return from_i128(*a as i128 * *d as i128, *b as i128 * *c as i128);
        }
        Q::normalise(self.to_big() / o.to_big())
    }

    pub fn floor(&self) -> Q {
        match self {
            Q::S(n, d) => Q::S(n.div_euclid(*d), 1),
            Q::B(b) => Q::normalise(b.floor()),
        }
    }

    pub fn ceil(&self) -> Q {
        match self {
            Q::S(n, d) => {
                let f = n.div_euclid(*d);
                Q::S(if n.rem_euclid(*d) == 0 { f } else { f + 1 }, 1)
            }
            Q::B(b) => Q::normalise(b.ceil()),
        }
    }

    /// Numerator and denominator as arbitrary-precision integers.
    pub fn parts(&self) -> (BigInt, BigInt) {
        match self {
            Q::S(n, d) => (BigInt::from(*n), BigInt::from(*d)),
            Q::B(b) => (b.numer().clone(), b.denom().clone()),
        }
    }
}

impl PartialEq for Q {
    fn eq(&self, o: &Q) -> bool {
        self.cmp(o) == Ordering::Equal
    }
}

impl Eq for Q {}

impl PartialOrd for Q {
    fn partial_cmp(&self, o: &Q) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Q {
    fn cmp(&self, o: &Q) -> Ordering {
        if let (Q::S(a, b), Q::S(c, d)) = (self, o) {
            return (*a as i128 * *d as i128).cmp(&(*c as i128 * *b as i128));
        }
        self.to_big().cmp(&o.to_big())
    }
}

impl std::fmt::Display for Q {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Q::S(n, 1) => write!(f, "{n}"),
            Q::S(n, d) => write!(f, "{n}/{d}"),
            Q::B(b) => write!(f, "{b}"),
        }
    }
}

/// `c + k*delta` with `delta` an infinitesimal: the value domain of the simplex, where a
/// strict bound `x < 3` is the non-strict bound `x <= 3 - delta`. Ordered lexicographically.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct D {
    pub c: Q,
    pub k: Q,
}

impl D {
    pub fn zero() -> D {
        D {
            c: Q::zero(),
            k: Q::zero(),
        }
    }

    pub fn exact(c: Q) -> D {
        D { c, k: Q::zero() }
    }

    pub fn new(c: Q, k: Q) -> D {
        D { c, k }
    }

    pub fn add(&self, o: &D) -> D {
        D {
            c: self.c.add(&o.c),
            k: self.k.add(&o.k),
        }
    }

    pub fn sub(&self, o: &D) -> D {
        D {
            c: self.c.sub(&o.c),
            k: self.k.sub(&o.k),
        }
    }

    pub fn scale(&self, q: &Q) -> D {
        D {
            c: self.c.mul(q),
            k: self.k.mul(q),
        }
    }

    pub fn div_q(&self, q: &Q) -> D {
        D {
            c: self.c.div(q),
            k: self.k.div(q),
        }
    }
}

impl PartialOrd for D {
    fn partial_cmp(&self, o: &D) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for D {
    fn cmp(&self, o: &D) -> Ordering {
        self.c.cmp(&o.c).then_with(|| self.k.cmp(&o.k))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: i64) -> Q {
        from_i128(n as i128, d as i128)
    }

    #[test]
    fn arithmetic_matches_bigrational_across_the_overflow_boundary() {
        let samples: Vec<Q> = vec![
            q(0, 1),
            q(1, 3),
            q(-7, 2),
            q(i64::MAX, 1),
            q(i64::MIN + 1, 1),
            q(i64::MAX, 3),
            q(1, i64::MAX),
            q(-5, i64::MAX),
            q(123_456_789_012, 987_654_321),
        ];
        for a in &samples {
            for b in &samples {
                let (x, y) = (a.to_big(), b.to_big());
                assert_eq!(a.add(b).to_big(), &x + &y);
                assert_eq!(a.sub(b).to_big(), &x - &y);
                assert_eq!(a.mul(b).to_big(), &x * &y);
                if !b.is_zero() {
                    assert_eq!(a.div(b).to_big(), &x / &y);
                }
                assert_eq!(a.cmp(b), x.cmp(&y));
            }
            let x = a.to_big();
            assert_eq!(a.floor().to_big(), x.floor());
            assert_eq!(a.ceil().to_big(), x.ceil());
            assert_eq!(a.neg().to_big(), -x);
        }
    }

    #[test]
    fn delta_order_is_lexicographic() {
        let a = D::new(q(1, 1), q(-1, 1));
        let b = D::exact(q(1, 1));
        assert!(a < b);
        assert!(D::new(q(1, 1), q(5, 1)) < D::new(q(2, 1), q(-5, 1)));
    }
}
