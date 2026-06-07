use crate::ast::Expr;
use std::collections::BTreeMap;

pub trait Tactic {
    fn apply(&self, expr: Expr) -> Expr;
}

pub struct Simplifier;
impl Tactic for Simplifier {
    fn apply(&self, expr: Expr) -> Expr {
        Self::simplify(expr)
    }
}

pub struct SolveEqs;

impl Tactic for SolveEqs {
    fn apply(&self, expr: Expr) -> Expr {
        match expr {
            Expr::And(args) => {
                let mut substs = BTreeMap::new();
                let mut remaining = Vec::new();
                for arg in args {
                    if let Expr::Eq(a, b) = &arg {
                        let (var, term) = match (&**a, &**b) {
                            (Expr::Var(name, _), term) if !term.contains_var(name) => (name.clone(), term.clone()),
                            (term, Expr::Var(name, _)) if !term.contains_var(name) => (name.clone(), term.clone()),
                            _ => { remaining.push(arg); continue; }
                        };
                        substs.insert(var, term);
                    } else {
                        remaining.push(arg);
                    }
                }
                if substs.is_empty() { return Expr::And(remaining); }
                let mut finalized = Vec::new();
                for expr in remaining {
                    finalized.push(expr.substitute(&substs));
                }
                Expr::And(finalized)
            }
            _ => expr,
        }
    }
}

impl Simplifier {
    pub fn simplify(expr: Expr) -> Expr {
        // ... (el código existente de simplify)
        match expr {
            Expr::And(args) => {
                let mut new_args = Vec::new();
                for arg in args {
                    let simplified = Self::simplify(arg);
                    match simplified {
                        Expr::Bool(true) => continue,
                        Expr::Bool(false) => return Expr::Bool(false),
                        Expr::And(inner_args) => new_args.extend(inner_args),
                        _ => new_args.push(simplified),
                    }
                }
                if new_args.is_empty() { return Expr::Bool(true); }
                if new_args.len() == 1 { return new_args.remove(0); }
                new_args.sort_unstable();
                new_args.dedup();
                if new_args.len() == 1 { return new_args.remove(0); }
                Expr::And(new_args)
            }
            Expr::Or(args) => {
                let mut new_args = Vec::new();
                for arg in args {
                    let simplified = Self::simplify(arg);
                    match simplified {
                        Expr::Bool(false) => continue,
                        Expr::Bool(true) => return Expr::Bool(true),
                        Expr::Or(inner_args) => new_args.extend(inner_args),
                        _ => new_args.push(simplified),
                    }
                }
                if new_args.is_empty() { return Expr::Bool(false); }
                if new_args.len() == 1 { return new_args.remove(0); }
                new_args.sort_unstable();
                new_args.dedup();
                if new_args.len() == 1 { return new_args.remove(0); }
                Expr::Or(new_args)
            }
            Expr::Not(inner) => {
                let simplified = Self::simplify(*inner);
                match simplified {
                    Expr::Bool(b) => Expr::Bool(!b),
                    Expr::Not(double_inner) => *double_inner,
                    _ => Expr::Not(Box::new(simplified)),
                }
            }
            Expr::Add(args) => {
                let mut new_args = Vec::new();
                let mut const_sum = 0;
                for arg in args {
                    let simplified = Self::simplify(arg);
                    match simplified {
                        Expr::Int(val) => const_sum += val,
                        Expr::Add(inner_args) => {
                            for ia in inner_args {
                                if let Expr::Int(v) = ia { const_sum += v; } else { new_args.push(ia); }
                            }
                        }
                        _ => new_args.push(simplified),
                    }
                }
                if new_args.is_empty() { return Expr::Int(const_sum); }
                if const_sum != 0 {
                    new_args.push(Expr::Int(const_sum));
                }
                if new_args.len() == 1 { return new_args.remove(0); }
                new_args.sort_unstable();
                Expr::Add(new_args)
            }
            Expr::Sub(args) => {
                if args.is_empty() { return Expr::Int(0); }
                let mut simplified_args: Vec<Expr> = args.into_iter().map(Self::simplify).collect();
                if simplified_args.len() == 2 && simplified_args[1] == Expr::Int(0) { return simplified_args.remove(0); }
                if simplified_args.len() == 2 && simplified_args[0] == simplified_args[1] { return Expr::Int(0); }
                if simplified_args.len() == 2 {
                    if let (Expr::Int(a), Expr::Int(b)) = (&simplified_args[0], &simplified_args[1]) {
                        return Expr::Int(a - b);
                    }
                }
                Expr::Sub(simplified_args)
            }
            Expr::Mul(args) => {
                let mut new_args = Vec::new();
                let mut const_prod = 1;
                let mut has_const = false;
                for arg in args {
                    let simplified = Self::simplify(arg);
                    match simplified {
                        Expr::Int(0) => return Expr::Int(0),
                        Expr::Int(1) => continue,
                        Expr::Int(val) => { const_prod *= val; has_const = true; }
                        Expr::Mul(inner_args) => {
                            for ia in inner_args {
                                if let Expr::Int(v) = ia {
                                    if v == 0 { return Expr::Int(0); }
                                    if v != 1 { const_prod *= v; has_const = true; }
                                } else { new_args.push(ia); }
                            }
                        }
                        _ => new_args.push(simplified),
                    }
                }
                if new_args.is_empty() { return Expr::Int(if has_const { const_prod } else { 1 }); }
                if const_prod != 1 || (new_args.is_empty() && has_const) { new_args.push(Expr::Int(const_prod)); }
                if new_args.len() == 1 { return new_args.remove(0); }
                new_args.sort_unstable();
                Expr::Mul(new_args)
            }
            Expr::Lt(a, b) => {
                let sa = Self::simplify(*a);
                let sb = Self::simplify(*b);
                if let (Expr::Int(va), Expr::Int(vb)) = (&sa, &sb) { return Expr::Bool(va < vb); }
                Expr::Lt(Box::new(sa), Box::new(sb))
            }
            Expr::Le(a, b) => {
                let sa = Self::simplify(*a);
                let sb = Self::simplify(*b);
                if let (Expr::Int(va), Expr::Int(vb)) = (&sa, &sb) { return Expr::Bool(va <= vb); }
                Expr::Le(Box::new(sa), Box::new(sb))
            }
            Expr::Gt(a, b) => {
                let sa = Self::simplify(*a);
                let sb = Self::simplify(*b);
                if let (Expr::Int(va), Expr::Int(vb)) = (&sa, &sb) { return Expr::Bool(va > vb); }
                Expr::Gt(Box::new(sa), Box::new(sb))
            }
            Expr::Ge(a, b) => {
                let sa = Self::simplify(*a);
                let sb = Self::simplify(*b);
                if let (Expr::Int(va), Expr::Int(vb)) = (&sa, &sb) { return Expr::Bool(va >= vb); }
                Expr::Ge(Box::new(sa), Box::new(sb))
            }
            Expr::Eq(a, b) => {
                let mut sa = Self::simplify(*a);
                let mut sb = Self::simplify(*b);
                if sa == sb { return Expr::Bool(true); }
                if let (Expr::Bool(va), Expr::Bool(vb)) = (&sa, &sb) { return Expr::Bool(va == vb); }
                if let (Expr::Int(va), Expr::Int(vb)) = (&sa, &sb) { return Expr::Bool(va == vb); }
                if sa > sb { std::mem::swap(&mut sa, &mut sb); }
                Expr::Eq(Box::new(sa), Box::new(sb))
            }
            Expr::Implies(a, b) => Expr::Implies(Box::new(Self::simplify(*a)), Box::new(Self::simplify(*b))),
            Expr::Ite(c, t, e) => {
                let sc = Self::simplify(*c);
                if let Expr::Bool(val) = sc {
                    if val { return Self::simplify(*t); } else { return Self::simplify(*e); }
                }
                Expr::Ite(Box::new(sc), Box::new(Self::simplify(*t)), Box::new(Self::simplify(*e)))
            }
            _ => expr,
        }
    }
}

pub struct TacticEngine {
    tactics: Vec<Box<dyn Tactic>>,
}

impl Default for TacticEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl TacticEngine {
    pub fn new() -> Self {
        Self { tactics: Vec::new() }
    }
    
    pub fn add_tactic(&mut self, tactic: Box<dyn Tactic>) {
        self.tactics.push(tactic);
    }
    
    pub fn apply(&self, mut expr: Expr) -> Expr {
        for tactic in &self.tactics {
            expr = tactic.apply(expr);
        }
        expr
    }
}
