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
            | Expr::BvUle(_, _)
            | Expr::BvUlt(_, _)
            | Expr::BvSle(_, _)
            | Expr::BvSlt(_, _)
            | Expr::ForAll(_, _)
            | Expr::Exists(_, _) => Type::Bool,

            Expr::Int(_)
            | Expr::Add(_)
            | Expr::Sub(_)
            | Expr::Mul(_)
            | Expr::Div(_, _)
            | Expr::StrLen(_) => Type::Int,

            Expr::Real(_, _) => Type::Real,

            Expr::Var(_, ty) => ty.clone(),

            Expr::BvConst(_, w) => Type::BitVec(*w),
            Expr::BvAdd(a, _)
            | Expr::BvSub(a, _)
            | Expr::BvMul(a, _)
            | Expr::BvAnd(a, _)
            | Expr::BvOr(a, _)
            | Expr::BvXor(a, _)
            | Expr::BvNot(a)
            | Expr::BvShl(a, _)
            | Expr::BvLshr(a, _)
            | Expr::BvAshr(a, _) => a.get_type(),
            Expr::BvExtract(h, l, _) => Type::BitVec(h - l + 1),
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
                "fp.isNaN" | "fp.isInfinite" | "fp.isZero" => Type::Bool,
                _ => Type::Unknown,
            },
            Expr::App(_, _) => Type::Unknown,
            Expr::Ite(_, t, _) => t.get_type(),
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

    /// Product of two or more non-constant factors, or division by a non-constant.
    pub fn has_nonlinear_arith(&self) -> bool {
        fn is_const(e: &Expr) -> bool {
            match e {
                Expr::Int(_) | Expr::Real(_, _) => true,
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
            Expr::StrLen(a) => Expr::StrLen(b(a, f)),
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
