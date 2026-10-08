pub mod fp;

impl Expr {
    pub fn get_type(&self) -> Type {
        match self {
            Expr::Bool(_)
            | Expr::And(_)
            | Expr::Or(_)
            | Expr::Not(_)
            | Expr::Implies(_, _)
            | Expr::Eq(_, _)
            | Expr::Lt(_, _)
            | Expr::Le(_, _)
            | Expr::Gt(_, _)
            | Expr::Ge(_, _)
            | Expr::StrContains(_, _)
            | Expr::IsInt(_)
            | Expr::BvUle(_, _)
            | Expr::BvUlt(_, _)
            | Expr::BvSle(_, _)
            | Expr::BvSlt(_, _)
            | Expr::ForAll(_, _)
            | Expr::Exists(_, _) => Type::Bool,

            Expr::Int(_)
            | Expr::IntDiv(_, _)
            | Expr::IntMod(_, _)
            | Expr::ToInt(_)
            | Expr::StrLen(_) => Type::Int,

            // Arithmetic is Real as soon as one operand is; `/` is always Real.
            Expr::Add(args) | Expr::Sub(args) | Expr::Mul(args) => {
                if args.iter().any(|a| a.get_type() == Type::Real) {
                    Type::Real
                } else {
                    Type::Int
                }
            }
            Expr::Div(_, _) => Type::Real,

            Expr::Real(_, _) => Type::Real,
            Expr::BigRat(_, den) => {
                if den == "1" {
                    Type::Int
                } else {
                    Type::Real
                }
            }

            Expr::Var(_, ty) => ty.clone(),

            Expr::BvConst(_, w) => Type::BitVec(*w),
            Expr::BvAdd(a, _)
            | Expr::BvSub(a, _)
            | Expr::BvMul(a, _)
            | Expr::BvAnd(a, _)
            | Expr::BvOr(a, _)
            | Expr::BvXor(a, _)
            | Expr::BvNot(a)
            | Expr::BvNeg(a)
            | Expr::BvUdiv(a, _)
            | Expr::BvUrem(a, _)
            | Expr::BvSdiv(a, _)
            | Expr::BvSrem(a, _)
            | Expr::BvSmod(a, _)
            | Expr::BvRotl(_, a)
            | Expr::BvRotr(_, a)
            | Expr::BvShl(a, _)
            | Expr::BvLshr(a, _)
            | Expr::BvAshr(a, _) => a.get_type(),
            Expr::BvExtract(h, l, _) => Type::BitVec(h - l + 1),
            Expr::BvZeroExt(n, a) | Expr::BvSignExt(n, a) => match a.get_type() {
                Type::BitVec(w) => Type::BitVec(w + n),
                _ => Type::Unknown,
            },
            Expr::BvRepeat(n, a) => match a.get_type() {
                Type::BitVec(w) => Type::BitVec(w * n),
                _ => Type::Unknown,
            },
            Expr::BvConcat(a, b) => {
                if let (Type::BitVec(wa), Type::BitVec(wb)) = (a.get_type(), b.get_type()) {
                    Type::BitVec(wa + wb)
                } else {
                    Type::Unknown
                }
            }

            Expr::Select(a, _) => {
                if let Type::Array(_, ety) = a.get_type() {
                    *ety
                } else {
                    Type::Unknown
                }
            }
            Expr::Store(a, _, _) => a.get_type(),
            Expr::ConstArray(ty, _) => ty.clone(),

            Expr::StrConst(_) | Expr::StrConcat(_) => Type::String,

            Expr::App(name, args) if name == "fp" => match args.as_slice() {
                [Expr::BvConst(_, 1), Expr::BvConst(_, ebits), Expr::BvConst(_, sig_bits)] => {
                    Type::Float(fp::FloatSort {
                        exponent_bits: *ebits as u16,
                        significand_bits: (*sig_bits + 1) as u16,
                    })
                }
                _ => Type::Unknown,
            },
            Expr::App(name, args) if name.starts_with("fp.") => match name.as_str() {
                "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.sqrt" | "fp.neg" | "fp.abs" => args
                    .iter()
                    .find_map(|arg| match arg.get_type() {
                        Type::Float(sort) => Some(Type::Float(sort)),
                        _ => None,
                    })
                    .unwrap_or(Type::Unknown),
                "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
                | "fp.isNegative" | "fp.isPositive" | "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt"
                | "fp.geq" => Type::Bool,
                _ => Type::Unknown,
            },
            Expr::App(_, _) => Type::Unknown,
            Expr::Ite(_, t, e) => match (t.get_type(), e.get_type()) {
                (Type::Int, Type::Real) | (Type::Real, Type::Int) => Type::Real,
                (ty, _) => ty,
            },
        }
    }

    /// Canonical constant for an exact rational: `Int` when it is an integer that fits
    /// `i64`, otherwise `BigRat` (arbitrary precision in both directions).
    pub fn from_rational(r: &num_rational::BigRational) -> Expr {
        use num_traits::ToPrimitive;
        if r.is_integer() {
            if let Some(v) = r.numer().to_i64() {
                return Expr::Int(v);
            }
        }
        Expr::BigRat(r.numer().to_string(), r.denom().to_string())
    }

    /// Exact value of a numeric constant (`Int`, `Real`, `BigRat`), if this is one.
    pub fn as_rational(&self) -> Option<num_rational::BigRational> {
        use num_bigint::BigInt;
        use std::str::FromStr;
        match self {
            Expr::Int(i) => Some(num_rational::BigRational::from_integer(BigInt::from(*i))),
            Expr::Real(m, s) => Some(num_rational::BigRational::new(
                BigInt::from(*m),
                BigInt::from(10u8).pow(*s),
            )),
            Expr::BigRat(n, d) => {
                let (n, d) = (BigInt::from_str(n).ok()?, BigInt::from_str(d).ok()?);
                if num_traits::Zero::is_zero(&d) {
                    None
                } else {
                    Some(num_rational::BigRational::new(n, d))
                }
            }
            _ => None,
        }
    }

    /// Value of a closed numeric expression built from literals with `+ - * /`.
    pub fn as_constant(&self) -> Option<num_rational::BigRational> {
        use num_traits::Zero;
        match self {
            Expr::Int(_) | Expr::Real(_, _) | Expr::BigRat(_, _) => self.as_rational(),
            Expr::Add(v) => v
                .iter()
                .try_fold(num_rational::BigRational::zero(), |a, x| {
                    Some(a + x.as_constant()?)
                }),
            Expr::Mul(v) => v
                .iter()
                .try_fold(num_rational::BigRational::from_integer(1.into()), |a, x| {
                    Some(a * x.as_constant()?)
                }),
            Expr::Sub(v) => match v.as_slice() {
                [] => Some(num_rational::BigRational::zero()),
                [only] => Some(-only.as_constant()?),
                [first, rest @ ..] => rest
                    .iter()
                    .try_fold(first.as_constant()?, |a, x| Some(a - x.as_constant()?)),
            },
            Expr::Div(a, b) => {
                let d = b.as_constant()?;
                if d.is_zero() {
                    None
                } else {
                    Some(a.as_constant()? / d)
                }
            }
            _ => None,
        }
    }

    /// True if `pred` holds for this node or any descendant.
    pub fn any_subterm(&self, pred: &dyn Fn(&Expr) -> bool) -> bool {
        if pred(self) {
            return true;
        }
        let mut found = false;
        self.map_children(&mut |c| {
            if !found && c.any_subterm(pred) {
                found = true;
            }
            c.clone()
        });
        found
    }

    /// Nonlinear arithmetic the incremental linearization cannot handle: a division by a
    /// non-constant, or a product that is not a plain `x * y` of two variables.
    pub fn has_unhandled_nonlinear(&self) -> bool {
        fn is_const(e: &Expr) -> bool {
            e.as_constant().is_some()
        }
        self.any_subterm(&|e| match e {
            Expr::Mul(args) => {
                let non_const: Vec<&Expr> = args.iter().filter(|a| !is_const(a)).collect();
                // Fine: no product, one factor, or a plain `x * y` of two variables.
                !matches!(
                    non_const.as_slice(),
                    [] | [_] | [Expr::Var(_, _), Expr::Var(_, _)]
                )
            }
            Expr::Div(_, d) => !is_const(d),
            _ => false,
        })
    }

    /// Product of two or more non-constant factors, or division by a non-constant.
    pub fn has_nonlinear_arith(&self) -> bool {
        fn is_const(e: &Expr) -> bool {
            match e {
                Expr::Int(_) | Expr::Real(_, _) | Expr::BigRat(_, _) => true,
                Expr::Add(v) | Expr::Mul(v) | Expr::Sub(v) => v.iter().all(is_const),
                Expr::Div(a, b) => is_const(a) && is_const(b),
                _ => false,
            }
        }
        self.any_subterm(&|e| match e {
            Expr::Mul(args) => args.iter().filter(|a| !is_const(a)).count() >= 2,
            Expr::Div(_, d) => !is_const(d),
            _ => false,
        })
    }

    /// Rebuild this node with `f` applied to every direct child expression.
    /// Leaves (constants, variables) are returned unchanged. Binders keep their
    /// variable lists; only the body is mapped.
    pub fn map_children(&self, f: &mut dyn FnMut(&Expr) -> Expr) -> Expr {
        let b = |x: &Expr, f: &mut dyn FnMut(&Expr) -> Expr| Box::new(f(x));
        match self {
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Real(_, _)
            | Expr::BigRat(_, _)
            | Expr::Var(_, _)
            | Expr::BvConst(_, _)
            | Expr::StrConst(_) => self.clone(),
            Expr::And(v) => Expr::And(v.iter().map(&mut *f).collect()),
            Expr::Or(v) => Expr::Or(v.iter().map(&mut *f).collect()),
            Expr::Add(v) => Expr::Add(v.iter().map(&mut *f).collect()),
            Expr::Sub(v) => Expr::Sub(v.iter().map(&mut *f).collect()),
            Expr::Mul(v) => Expr::Mul(v.iter().map(&mut *f).collect()),
            Expr::StrConcat(v) => Expr::StrConcat(v.iter().map(&mut *f).collect()),
            Expr::App(n, v) => Expr::App(n.clone(), v.iter().map(&mut *f).collect()),
            Expr::Not(a) => Expr::Not(b(a, f)),
            Expr::BvNot(a) => Expr::BvNot(b(a, f)),
            Expr::BvNeg(a) => Expr::BvNeg(b(a, f)),
            Expr::BvZeroExt(n, a) => Expr::BvZeroExt(*n, b(a, f)),
            Expr::BvSignExt(n, a) => Expr::BvSignExt(*n, b(a, f)),
            Expr::BvRotl(n, a) => Expr::BvRotl(*n, b(a, f)),
            Expr::BvRotr(n, a) => Expr::BvRotr(*n, b(a, f)),
            Expr::BvRepeat(n, a) => Expr::BvRepeat(*n, b(a, f)),
            Expr::BvUdiv(x, y) => Expr::BvUdiv(b(x, f), b(y, f)),
            Expr::BvUrem(x, y) => Expr::BvUrem(b(x, f), b(y, f)),
            Expr::BvSdiv(x, y) => Expr::BvSdiv(b(x, f), b(y, f)),
            Expr::BvSrem(x, y) => Expr::BvSrem(b(x, f), b(y, f)),
            Expr::BvSmod(x, y) => Expr::BvSmod(b(x, f), b(y, f)),
            Expr::StrLen(a) => Expr::StrLen(b(a, f)),
            Expr::ToInt(a) => Expr::ToInt(b(a, f)),
            Expr::ConstArray(ty, a) => Expr::ConstArray(ty.clone(), b(a, f)),
            Expr::IsInt(a) => Expr::IsInt(b(a, f)),
            Expr::IntDiv(x, y) => Expr::IntDiv(b(x, f), b(y, f)),
            Expr::IntMod(x, y) => Expr::IntMod(b(x, f), b(y, f)),
            Expr::BvExtract(h, l, a) => Expr::BvExtract(*h, *l, b(a, f)),
            Expr::Implies(x, y) => Expr::Implies(b(x, f), b(y, f)),
            Expr::Eq(x, y) => Expr::Eq(b(x, f), b(y, f)),
            Expr::Lt(x, y) => Expr::Lt(b(x, f), b(y, f)),
            Expr::Le(x, y) => Expr::Le(b(x, f), b(y, f)),
            Expr::Gt(x, y) => Expr::Gt(b(x, f), b(y, f)),
            Expr::Ge(x, y) => Expr::Ge(b(x, f), b(y, f)),
            Expr::Div(x, y) => Expr::Div(b(x, f), b(y, f)),
            Expr::BvAdd(x, y) => Expr::BvAdd(b(x, f), b(y, f)),
            Expr::BvSub(x, y) => Expr::BvSub(b(x, f), b(y, f)),
            Expr::BvMul(x, y) => Expr::BvMul(b(x, f), b(y, f)),
            Expr::BvAnd(x, y) => Expr::BvAnd(b(x, f), b(y, f)),
            Expr::BvOr(x, y) => Expr::BvOr(b(x, f), b(y, f)),
            Expr::BvXor(x, y) => Expr::BvXor(b(x, f), b(y, f)),
            Expr::BvShl(x, y) => Expr::BvShl(b(x, f), b(y, f)),
            Expr::BvLshr(x, y) => Expr::BvLshr(b(x, f), b(y, f)),
            Expr::BvAshr(x, y) => Expr::BvAshr(b(x, f), b(y, f)),
            Expr::BvUle(x, y) => Expr::BvUle(b(x, f), b(y, f)),
            Expr::BvUlt(x, y) => Expr::BvUlt(b(x, f), b(y, f)),
            Expr::BvSle(x, y) => Expr::BvSle(b(x, f), b(y, f)),
            Expr::BvSlt(x, y) => Expr::BvSlt(b(x, f), b(y, f)),
            Expr::BvConcat(x, y) => Expr::BvConcat(b(x, f), b(y, f)),
            Expr::Select(x, y) => Expr::Select(b(x, f), b(y, f)),
            Expr::StrContains(x, y) => Expr::StrContains(b(x, f), b(y, f)),
            Expr::Ite(c, t, e) => Expr::Ite(b(c, f), b(t, f), b(e, f)),
            Expr::Store(x, y, z) => Expr::Store(b(x, f), b(y, f), b(z, f)),
            Expr::ForAll(vs, body) => Expr::ForAll(vs.clone(), b(body, f)),
            Expr::Exists(vs, body) => Expr::Exists(vs.clone(), b(body, f)),
        }
    }

    pub fn substitute(&self, vars: &BTreeMap<String, Expr>) -> Expr {
        match self {
            Expr::Var(name, _) => {
                if let Some(replacement) = vars.get(name) {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Expr::And(args) => Expr::And(args.iter().map(|a| a.substitute(vars)).collect()),
            Expr::Or(args) => Expr::Or(args.iter().map(|a| a.substitute(vars)).collect()),
            Expr::Not(inner) => Expr::Not(Box::new(inner.substitute(vars))),
            Expr::Implies(a, b) => {
                Expr::Implies(Box::new(a.substitute(vars)), Box::new(b.substitute(vars)))
            }
            Expr::Eq(a, b) => Expr::Eq(Box::new(a.substitute(vars)), Box::new(b.substitute(vars))),
            Expr::Add(args) => Expr::Add(args.iter().map(|a| a.substitute(vars)).collect()),
            Expr::App(name, args) => Expr::App(
                name.clone(),
                args.iter().map(|a| a.substitute(vars)).collect(),
            ),
            Expr::Select(a, i) => {
                Expr::Select(Box::new(a.substitute(vars)), Box::new(i.substitute(vars)))
            }
            Expr::Store(a, i, v) => Expr::Store(
                Box::new(a.substitute(vars)),
                Box::new(i.substitute(vars)),
                Box::new(v.substitute(vars)),
            ),
            _ => self.clone(),
        }
    }

    pub fn contains_var(&self, name: &str) -> bool {
        match self {
            Expr::Var(n, _) => n == name,
            Expr::And(args) | Expr::Or(args) | Expr::Add(args) | Expr::Mul(args) => {
                args.iter().any(|a| a.contains_var(name))
            }
            Expr::Not(inner) | Expr::BvNot(inner) | Expr::StrLen(inner) => inner.contains_var(name),
            Expr::Implies(a, b)
            | Expr::Eq(a, b)
            | Expr::Lt(a, b)
            | Expr::Le(a, b)
            | Expr::Gt(a, b)
            | Expr::Ge(a, b)
            | Expr::Div(a, b)
            | Expr::BvAdd(a, b)
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
            | Expr::BvSlt(a, b)
            | Expr::BvConcat(a, b)
            | Expr::Select(a, b)
            | Expr::StrContains(a, b) => a.contains_var(name) || b.contains_var(name),
            Expr::Ite(c, t, e) | Expr::Store(c, t, e) => {
                c.contains_var(name) || t.contains_var(name) || e.contains_var(name)
            }
            Expr::App(_, args) => args.iter().any(|a| a.contains_var(name)),
            _ => false,
        }
    }
}

use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum Expr {
    Bool(bool),
    Int(i64),
    Real(i64, u32), // Integer part and decimal scale
    /// Exact rational constant that does not fit `Int`/`Real`: canonical decimal
    /// `numerator` (signed) and `denominator` (positive, coprime to the numerator).
    /// Built with [`Expr::from_rational`]; read back with [`Expr::as_rational`].
    BigRat(String, String),
    Var(String, Type),
    And(Vec<Expr>),
    Or(Vec<Expr>),
    Not(Box<Expr>),
    Implies(Box<Expr>, Box<Expr>),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>), // If-Then-Else
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>), // Less than
    Le(Box<Expr>, Box<Expr>), // Lower or equal
    Gt(Box<Expr>, Box<Expr>), // Greater than
    Ge(Box<Expr>, Box<Expr>), // Greater or equal
    Add(Vec<Expr>),
    Sub(Vec<Expr>),
    Mul(Vec<Expr>),
    Div(Box<Expr>, Box<Expr>),
    /// SMT-LIB integer `div` / `mod` (Euclidean) and `to_int` / `is_int`.
    IntDiv(Box<Expr>, Box<Expr>),
    IntMod(Box<Expr>, Box<Expr>),
    ToInt(Box<Expr>),
    IsInt(Box<Expr>),
    App(String, Vec<Expr>), // Function application
    // Bit-vectors
    BvConst(u64, usize), // Value and width
    BvAdd(Box<Expr>, Box<Expr>),
    BvSub(Box<Expr>, Box<Expr>),
    BvMul(Box<Expr>, Box<Expr>),
    BvAnd(Box<Expr>, Box<Expr>),
    BvOr(Box<Expr>, Box<Expr>),
    BvXor(Box<Expr>, Box<Expr>),
    BvNot(Box<Expr>),
    BvNeg(Box<Expr>),
    BvUdiv(Box<Expr>, Box<Expr>),
    BvUrem(Box<Expr>, Box<Expr>),
    BvSdiv(Box<Expr>, Box<Expr>),
    BvSrem(Box<Expr>, Box<Expr>),
    BvSmod(Box<Expr>, Box<Expr>),
    /// `((_ zero_extend n) x)`, `sign_extend`, `rotate_left`, `rotate_right`, `repeat`.
    BvZeroExt(usize, Box<Expr>),
    BvSignExt(usize, Box<Expr>),
    BvRotl(usize, Box<Expr>),
    BvRotr(usize, Box<Expr>),
    BvRepeat(usize, Box<Expr>),
    BvShl(Box<Expr>, Box<Expr>),
    BvLshr(Box<Expr>, Box<Expr>),
    BvAshr(Box<Expr>, Box<Expr>),
    BvUle(Box<Expr>, Box<Expr>),
    BvUlt(Box<Expr>, Box<Expr>),
    BvSle(Box<Expr>, Box<Expr>),
    BvSlt(Box<Expr>, Box<Expr>),
    BvExtract(usize, usize, Box<Expr>), // high, low, expr
    BvConcat(Box<Expr>, Box<Expr>),
    // Arrays
    /// `((as const (Array I E)) v)`: the array that maps every index to `v`.
    ConstArray(Type, Box<Expr>),
    Select(Box<Expr>, Box<Expr>),           // Array, Index
    Store(Box<Expr>, Box<Expr>, Box<Expr>), // Array, Index, Value
    // Quantifiers
    ForAll(Vec<(String, Type)>, Box<Expr>), // Bound variables and body
    Exists(Vec<(String, Type)>, Box<Expr>),
    // Strings
    StrConst(String),
    StrConcat(Vec<Expr>),
    StrLen(Box<Expr>),
    StrContains(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum Type {
    Unknown,
    Bool,
    Int,
    Real,
    Float(fp::FloatSort),
    BitVec(usize),
    String,
    /// User-declared uninterpreted sort (`declare-sort`).
    Sort(String),
    Array(Box<Type>, Box<Type>), // Index Type, Element Type
    Fn(Vec<Type>, Box<Type>),    // Function type
}

#[derive(Debug, Clone)]
pub enum ModelValue {
    Bool(bool),
    Int(BigInt),
    Real(num_rational::BigRational),
    BitVec(u64, usize),
    /// Valor de modelo de punto flotante IEEE-754 exacto (contrato compartido con theory::fp).
    Float(fp::FloatValue),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Bool(b) => write!(f, "{}", b),
            Expr::Int(i) => write!(f, "{}", i),
            Expr::Real(i, s) => write!(f, "{}.{}", i, s),
            Expr::Var(s, _) => write!(f, "{}", s),
            Expr::And(v) => write!(f, "(and {:?})", v),
            Expr::Or(v) => write!(f, "(or {:?})", v),
            Expr::Not(e) => write!(f, "(not {})", e),
            Expr::Implies(a, b) => write!(f, "(=> {} {})", a, b),
            Expr::Ite(c, t, e) => write!(f, "(ite {} {} {})", c, t, e),
            Expr::Eq(a, b) => write!(f, "(= {} {})", a, b),
            Expr::Lt(a, b) => write!(f, "(< {} {})", a, b),
            Expr::Le(a, b) => write!(f, "(<= {} {})", a, b),
            Expr::Gt(a, b) => write!(f, "(> {} {})", a, b),
            Expr::Ge(a, b) => write!(f, "(>= {} {})", a, b),
            Expr::Add(v) => write!(f, "(+ {:?})", v),
            Expr::Sub(v) => write!(f, "(- {:?})", v),
            Expr::Mul(v) => write!(f, "(* {:?})", v),
            Expr::Div(a, b) => write!(f, "(/ {} {})", a, b),
            Expr::App(s, args) => write!(f, "({} {:?})", s, args),
            Expr::BvConst(v, w) => write!(f, "(_ bv{} {})", v, w),
            Expr::BvAdd(a, b) => write!(f, "(bvadd {} {})", a, b),
            Expr::BvAnd(a, b) => write!(f, "(bvand {} {})", a, b),
            Expr::BvExtract(h, l, e) => write!(f, "((_ extract {} {}) {})", h, l, e),
            Expr::Select(a, i) => write!(f, "(select {} {})", a, i),
            Expr::Store(a, i, v) => write!(f, "(store {} {} {})", a, i, v),
            Expr::ForAll(vars, body) => write!(f, "(forall {:?} {})", vars, body),
            Expr::Exists(vars, body) => write!(f, "(exists {:?} {})", vars, body),
            Expr::StrConst(s) => write!(f, "\"{}\"", s),
            Expr::StrConcat(v) => write!(f, "(str.++ {:?})", v),
            Expr::StrLen(s) => write!(f, "(str.len {})", s),
            Expr::StrContains(a, b) => write!(f, "(str.contains {} {})", a, b),
            _ => write!(f, "{:?}", self),
        }
    }
}
