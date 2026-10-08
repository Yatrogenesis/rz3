//! Exact evaluation of ground formulas under a model.
//!
//! Used as an independent check on satisfiable verdicts: before `check()` reports
//! `Sat`, every assertion the theories were given is evaluated with the model the
//! solver extracted. A formula that evaluates to false means some component (SAT core,
//! simplex, bit-blaster, model extraction) is wrong, and the verdict is downgraded to
//! `Unknown` instead of being reported.

use crate::ast::{Expr, ModelValue, Type};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    Num(BigRational),
    Bv(u64, usize),
}

fn mask(width: usize) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn signed(v: u64, width: usize) -> i128 {
    if width > 0 && width <= 64 && (v >> (width - 1)) & 1 == 1 {
        i128::from(v) - (1i128 << width)
    } else {
        i128::from(v)
    }
}

fn decimal(mantissa: i64, scale: u32) -> BigRational {
    BigRational::new(BigInt::from(mantissa), BigInt::from(10).pow(scale))
}

fn default_value(ty: &Type) -> Option<Value> {
    match ty {
        Type::Bool => Some(Value::Bool(false)),
        Type::Int | Type::Real => Some(Value::Num(BigRational::zero())),
        Type::BitVec(w) => Some(Value::Bv(0, *w)),
        _ => None,
    }
}

fn bool_of(v: Option<Value>) -> Option<bool> {
    match v {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    }
}

/// Evaluate `expr`; `None` when it contains something this evaluator does not interpret
/// (uninterpreted applications, arrays, strings, floating point, quantifiers, ...).
pub fn eval(expr: &Expr, model: &BTreeMap<String, ModelValue>) -> Option<Value> {
    ev(expr, model, &FunTable::new())
}

/// Interpretation of uninterpreted functions: name -> (argument values -> result).
pub type FunTable = BTreeMap<String, Vec<(Vec<Value>, Value)>>;

/// Like [`eval`], with declared functions interpreted by `funs`.
pub fn eval_with(
    expr: &Expr,
    model: &BTreeMap<String, ModelValue>,
    funs: &FunTable,
) -> Option<Value> {
    ev(expr, model, funs)
}

fn ev(expr: &Expr, model: &BTreeMap<String, ModelValue>, funs: &FunTable) -> Option<Value> {
    match expr {
        Expr::App(name, args) => {
            let values: Option<Vec<Value>> = args.iter().map(|a| ev(a, model, funs)).collect();
            let values = values?;
            funs.get(name)?
                .iter()
                .find(|(known, _)| *known == values)
                .map(|(_, result)| result.clone())
        }
        Expr::Bool(b) => Some(Value::Bool(*b)),
        Expr::Int(i) => Some(Value::Num(BigRational::from_integer(BigInt::from(*i)))),
        Expr::Real(m, s) => Some(Value::Num(decimal(*m, *s))),
        Expr::BigRat(_, _) => expr.as_rational().map(Value::Num),
        Expr::BvConst(v, w) => Some(Value::Bv(*v & mask(*w), *w)),
        Expr::Var(name, ty) => match model.get(name) {
            Some(ModelValue::Bool(b)) => Some(Value::Bool(*b)),
            Some(ModelValue::Int(i)) => Some(Value::Num(BigRational::from_integer(i.clone()))),
            Some(ModelValue::Real(r)) => Some(Value::Num(r.clone())),
            Some(ModelValue::BitVec(v, w)) => match ty {
                // The model's width is the highest bit seen; trust the declared sort.
                Type::BitVec(declared) => Some(Value::Bv(*v & mask(*declared), *declared)),
                _ => Some(Value::Bv(*v, *w)),
            },
            Some(ModelValue::Float(_)) => None,
            None => default_value(ty),
        },
        Expr::Not(a) => Some(Value::Bool(!bool_of(ev(a, model, funs))?)),
        Expr::And(args) => {
            let mut all = true;
            for a in args {
                all &= bool_of(ev(a, model, funs))?;
            }
            Some(Value::Bool(all))
        }
        Expr::Or(args) => {
            let mut any = false;
            for a in args {
                any |= bool_of(ev(a, model, funs))?;
            }
            Some(Value::Bool(any))
        }
        Expr::Implies(a, b) => {
            let (x, y) = (bool_of(ev(a, model, funs))?, bool_of(ev(b, model, funs))?);
            Some(Value::Bool(!x || y))
        }
        Expr::Ite(c, t, e) => {
            if bool_of(ev(c, model, funs))? {
                ev(t, model, funs)
            } else {
                ev(e, model, funs)
            }
        }
        Expr::Eq(a, b) => Some(Value::Bool(ev(a, model, funs)? == ev(b, model, funs)?)),
        Expr::Lt(a, b) | Expr::Le(a, b) | Expr::Gt(a, b) | Expr::Ge(a, b) => {
            let (Value::Num(x), Value::Num(y)) = (ev(a, model, funs)?, ev(b, model, funs)?) else {
                return None;
            };
            Some(Value::Bool(match expr {
                Expr::Lt(_, _) => x < y,
                Expr::Le(_, _) => x <= y,
                Expr::Gt(_, _) => x > y,
                _ => x >= y,
            }))
        }
        Expr::Add(args) => {
            let mut sum = BigRational::zero();
            for a in args {
                let Value::Num(v) = ev(a, model, funs)? else {
                    return None;
                };
                sum += v;
            }
            Some(Value::Num(sum))
        }
        Expr::Mul(args) => {
            let mut prod = BigRational::one();
            for a in args {
                let Value::Num(v) = ev(a, model, funs)? else {
                    return None;
                };
                prod *= v;
            }
            Some(Value::Num(prod))
        }
        Expr::Sub(args) => {
            let (first, rest) = args.split_first()?;
            let Value::Num(mut acc) = ev(first, model, funs)? else {
                return None;
            };
            if rest.is_empty() {
                return Some(Value::Num(-acc));
            }
            for a in rest {
                let Value::Num(v) = ev(a, model, funs)? else {
                    return None;
                };
                acc -= v;
            }
            Some(Value::Num(acc))
        }
        Expr::Div(a, b) => {
            let (Value::Num(x), Value::Num(y)) = (ev(a, model, funs)?, ev(b, model, funs)?) else {
                return None;
            };
            if y.is_zero() {
                None
            } else {
                Some(Value::Num(x / y))
            }
        }
        Expr::IntDiv(a, b) | Expr::IntMod(a, b) => {
            let (Value::Num(x), Value::Num(c)) = (ev(a, model, funs)?, ev(b, model, funs)?) else {
                return None;
            };
            if c.is_zero() || !x.is_integer() || !c.is_integer() {
                return None;
            }
            // Euclidean: x = c*q + r with 0 <= r < |c|.
            let q = if c > BigRational::zero() {
                (x.clone() / c.clone()).floor()
            } else {
                (x.clone() / c.clone()).ceil()
            };
            Some(Value::Num(if matches!(expr, Expr::IntDiv(_, _)) {
                q
            } else {
                x - c * q
            }))
        }
        Expr::ToInt(a) => {
            let Value::Num(x) = ev(a, model, funs)? else {
                return None;
            };
            Some(Value::Num(x.floor()))
        }
        Expr::IsInt(a) => {
            let Value::Num(x) = ev(a, model, funs)? else {
                return None;
            };
            Some(Value::Bool(x.is_integer()))
        }
        Expr::BvNeg(a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            Some(Value::Bv(v.wrapping_neg() & mask(w), w))
        }
        Expr::BvZeroExt(n, a) | Expr::BvSignExt(n, a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            if w + n > 64 {
                return None;
            }
            let extended = if matches!(expr, Expr::BvSignExt(_, _)) {
                (signed(v, w) as u64) & mask(w + n)
            } else {
                v
            };
            Some(Value::Bv(extended, w + n))
        }
        Expr::BvRotl(n, a) | Expr::BvRotr(n, a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            let k = n % w;
            let left = if matches!(expr, Expr::BvRotl(_, _)) {
                k
            } else {
                (w - k) % w
            };
            let rotated = if left == 0 {
                v
            } else {
                ((v << left) | (v >> (w - left))) & mask(w)
            };
            Some(Value::Bv(rotated, w))
        }
        Expr::BvRepeat(n, a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            if w * n > 64 || *n == 0 {
                return None;
            }
            let mut out = 0u64;
            for _ in 0..*n {
                out = (out << w) | v;
            }
            Some(Value::Bv(out, w * n))
        }
        Expr::BvUdiv(a, b)
        | Expr::BvUrem(a, b)
        | Expr::BvSdiv(a, b)
        | Expr::BvSrem(a, b)
        | Expr::BvSmod(a, b) => {
            let (Value::Bv(x, w), Value::Bv(y, wy)) = (ev(a, model, funs)?, ev(b, model, funs)?)
            else {
                return None;
            };
            if w != wy {
                return None;
            }
            let m = mask(w);
            let (sx, sy) = (signed(x, w), signed(y, w));
            let out = match expr {
                // SMT-LIB: x / 0 is all ones and x % 0 is x.
                Expr::BvUdiv(_, _) => x.checked_div(y).unwrap_or(m),
                Expr::BvUrem(_, _) => x.checked_rem(y).unwrap_or(x),
                Expr::BvSdiv(_, _) => {
                    if y == 0 {
                        if sx < 0 {
                            1
                        } else {
                            m
                        }
                    } else {
                        (sx.wrapping_div(sy) as u64) & m
                    }
                }
                Expr::BvSrem(_, _) => {
                    if y == 0 {
                        x
                    } else {
                        (sx.wrapping_rem(sy) as u64) & m
                    }
                }
                _ => {
                    // bvsmod: result takes the sign of the divisor
                    if y == 0 {
                        x
                    } else {
                        let r = sx.rem_euclid(sy.abs());
                        let r = if sy < 0 && r != 0 { r + sy } else { r };
                        (r as u64) & m
                    }
                }
            };
            Some(Value::Bv(out, w))
        }
        Expr::BvNot(a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            Some(Value::Bv(!v & mask(w), w))
        }
        Expr::BvExtract(h, l, a) => {
            let Value::Bv(v, w) = ev(a, model, funs)? else {
                return None;
            };
            if l > h || *h >= w {
                return None;
            }
            let width = h - l + 1;
            Some(Value::Bv((v >> l) & mask(width), width))
        }
        Expr::BvConcat(a, b) => {
            let (Value::Bv(hi, wh), Value::Bv(lo, wl)) = (ev(a, model, funs)?, ev(b, model, funs)?)
            else {
                return None;
            };
            if wh + wl > 64 {
                return None;
            }
            Some(Value::Bv((hi << wl) | lo, wh + wl))
        }
        Expr::BvAdd(a, b)
        | Expr::BvSub(a, b)
        | Expr::BvMul(a, b)
        | Expr::BvAnd(a, b)
        | Expr::BvOr(a, b)
        | Expr::BvXor(a, b)
        | Expr::BvShl(a, b)
        | Expr::BvLshr(a, b)
        | Expr::BvAshr(a, b)
        | Expr::BvUle(a, b)
        | Expr::BvUlt(a, b)
        | Expr::BvSle(a, b)
        | Expr::BvSlt(a, b) => {
            let (Value::Bv(x, w), Value::Bv(y, wy)) = (ev(a, model, funs)?, ev(b, model, funs)?)
            else {
                return None;
            };
            if w != wy {
                return None;
            }
            let m = mask(w);
            let shift = |left: bool, arithmetic: bool| -> u64 {
                if y >= w as u64 {
                    if arithmetic && (x >> (w - 1)) & 1 == 1 {
                        m
                    } else {
                        0
                    }
                } else if left {
                    (x << y) & m
                } else if arithmetic {
                    ((signed(x, w) >> y) as u64) & m
                } else {
                    x >> y
                }
            };
            Some(match expr {
                Expr::BvAdd(_, _) => Value::Bv(x.wrapping_add(y) & m, w),
                Expr::BvSub(_, _) => Value::Bv(x.wrapping_sub(y) & m, w),
                Expr::BvMul(_, _) => Value::Bv(x.wrapping_mul(y) & m, w),
                Expr::BvAnd(_, _) => Value::Bv(x & y, w),
                Expr::BvOr(_, _) => Value::Bv(x | y, w),
                Expr::BvXor(_, _) => Value::Bv(x ^ y, w),
                Expr::BvShl(_, _) => Value::Bv(shift(true, false), w),
                Expr::BvLshr(_, _) => Value::Bv(shift(false, false), w),
                Expr::BvAshr(_, _) => Value::Bv(shift(false, true), w),
                Expr::BvUle(_, _) => Value::Bool(x <= y),
                Expr::BvUlt(_, _) => Value::Bool(x < y),
                Expr::BvSle(_, _) => Value::Bool(signed(x, w) <= signed(y, w)),
                _ => Value::Bool(signed(x, w) < signed(y, w)),
            })
        }
        _ => None,
    }
}

/// Outcome of checking one assertion against a model.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Verdict {
    True,
    False,
    /// Contains something the evaluator does not interpret.
    Unknown,
}

pub fn holds(expr: &Expr, model: &BTreeMap<String, ModelValue>, funs: &FunTable) -> Verdict {
    match ev(expr, model, funs) {
        Some(Value::Bool(true)) => Verdict::True,
        Some(Value::Bool(false)) => Verdict::False,
        _ => Verdict::Unknown,
    }
}
