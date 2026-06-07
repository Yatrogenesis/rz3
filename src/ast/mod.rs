impl Expr {
    pub fn get_type(&self) -> Type {
        match self {
            Expr::Bool(_) | Expr::And(_) | Expr::Or(_) | Expr::Not(_) | Expr::Implies(_, _) |
            Expr::Eq(_, _) | Expr::Lt(_, _) | Expr::Le(_, _) | Expr::Gt(_, _) | Expr::Ge(_, _) |
            Expr::StrContains(_, _) | Expr::BvUle(_, _) | Expr::BvUlt(_, _) | 
            Expr::BvSle(_, _) | Expr::BvSlt(_, _) | Expr::ForAll(_, _) | Expr::Exists(_, _) => Type::Bool,
            
            Expr::Int(_) | Expr::Add(_) | Expr::Sub(_) | Expr::Mul(_) | Expr::Div(_, _) |
            Expr::StrLen(_) => Type::Int,
            
            Expr::Real(_, _) => Type::Real,
            
            Expr::Var(_, ty) => ty.clone(),
            
            Expr::BvConst(_, w) => Type::BitVec(*w),
            Expr::BvAdd(a, _) | Expr::BvSub(a, _) | Expr::BvMul(a, _) |
            Expr::BvAnd(a, _) | Expr::BvOr(a, _) | Expr::BvXor(a, _) |
            Expr::BvNot(a) | Expr::BvShl(a, _) | Expr::BvLshr(a, _) |
            Expr::BvAshr(a, _) => a.get_type(),
            Expr::BvExtract(h, l, _) => Type::BitVec(h - l + 1),
            Expr::BvConcat(a, b) => {
                if let (Type::BitVec(wa), Type::BitVec(wb)) = (a.get_type(), b.get_type()) {
                    Type::BitVec(wa + wb)
                } else {
                    Type::BitVec(0)
                }
            }
            
            Expr::Select(a, _) => {
                if let Type::Array(_, ety) = a.get_type() {
                    *ety
                } else {
                    Type::Int // Fallback
                }
            }
            Expr::Store(a, _, _) => a.get_type(),
            
            Expr::StrConst(_) | Expr::StrConcat(_) => Type::String,
            
            Expr::App(_, _) => Type::Int, // Simplificación: asumir Int por ahora o usar symbol table
            Expr::Ite(_, t, _) => t.get_type(),
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
            Expr::Implies(a, b) => Expr::Implies(Box::new(a.substitute(vars)), Box::new(b.substitute(vars))),
            Expr::Eq(a, b) => Expr::Eq(Box::new(a.substitute(vars)), Box::new(b.substitute(vars))),
            Expr::Add(args) => Expr::Add(args.iter().map(|a| a.substitute(vars)).collect()),
            Expr::App(name, args) => Expr::App(name.clone(), args.iter().map(|a| a.substitute(vars)).collect()),
            Expr::Select(a, i) => Expr::Select(Box::new(a.substitute(vars)), Box::new(i.substitute(vars))),
            Expr::Store(a, i, v) => Expr::Store(Box::new(a.substitute(vars)), Box::new(i.substitute(vars)), Box::new(v.substitute(vars))),
            _ => self.clone(),
        }
    }

    pub fn contains_var(&self, name: &str) -> bool {
        match self {
            Expr::Var(n, _) => n == name,
            Expr::And(args) | Expr::Or(args) | Expr::Add(args) | Expr::Mul(args) => args.iter().any(|a| a.contains_var(name)),
            Expr::Not(inner) | Expr::BvNot(inner) | Expr::StrLen(inner) => inner.contains_var(name),
            Expr::Implies(a, b) | Expr::Eq(a, b) | Expr::Lt(a, b) | Expr::Le(a, b) | Expr::Gt(a, b) | Expr::Ge(a, b) | 
            Expr::Div(a, b) | Expr::BvAdd(a, b) | Expr::BvSub(a, b) | Expr::BvMul(a, b) | 
            Expr::BvAnd(a, b) | Expr::BvOr(a, b) | Expr::BvXor(a, b) | Expr::BvShl(a, b) | Expr::BvLshr(a, b) | Expr::BvAshr(a, b) | 
            Expr::BvUle(a, b) | Expr::BvUlt(a, b) | Expr::BvSle(a, b) | Expr::BvSlt(a, b) | Expr::BvConcat(a, b) | 
            Expr::Select(a, b) | Expr::StrContains(a, b) => a.contains_var(name) || b.contains_var(name),
            Expr::Ite(c, t, e) | Expr::Store(c, t, e) => c.contains_var(name) || t.contains_var(name) || e.contains_var(name),
            Expr::App(_, args) => args.iter().any(|a| a.contains_var(name)),
            _ => false,
        }
    }
}

use std::collections::BTreeMap;
use std::fmt;

use serde::{Serialize, Deserialize};

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
    Select(Box<Expr>, Box<Expr>),        // Array, Index
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
    Bool,
    Int,
    Real,
    BitVec(usize),
    String,
    Array(Box<Type>, Box<Type>), // Index Type, Element Type
    Fn(Vec<Type>, Box<Type>), // Function type
}

#[derive(Debug, Clone)]
pub enum ModelValue {
    Bool(bool),
    Int(i64),
    Real(num_rational::BigRational),
    BitVec(u64, usize),
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
