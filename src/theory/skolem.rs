//! Negation normal form and skolemisation for quantified formulas.
//!
//! An existential quantifier cannot be handed to the SAT core as an opaque atom: that makes
//! `exists x. false` satisfiable. Quantified formulas are therefore rewritten first:
//!
//! * negations are pushed to the atoms (`!forall` becomes `exists`, and so on);
//! * every existential in positive position becomes a fresh constant, or a fresh function of
//!   the universals that enclose it (skolemisation preserves satisfiability);
//! * what remains is universals in positive position, which the instantiation machinery
//!   handles. A satisfiable verdict is never reported while one remains, because instances
//!   of a universal can refute a model but never prove it.
//!
//! The pass only touches formulas that contain a quantifier.

use crate::ast::{Expr, Type};

#[derive(Default)]
pub struct Skolemizer {
    fresh: usize,
}

fn not(e: Expr) -> Expr {
    Expr::Not(Box::new(e))
}

/// Replace free occurrences of the variable `name` in `e` by `with`.
pub fn substitute(e: &Expr, name: &str, with: &Expr) -> Expr {
    match e {
        Expr::Var(n, _) if n == name => with.clone(),
        Expr::ForAll(vars, body) | Expr::Exists(vars, body) => {
            if vars.iter().any(|(v, _)| v == name) {
                return e.clone(); // shadowed
            }
            let body = Box::new(substitute(body, name, with));
            if matches!(e, Expr::ForAll(_, _)) {
                Expr::ForAll(vars.clone(), body)
            } else {
                Expr::Exists(vars.clone(), body)
            }
        }
        _ => e.map_children(&mut |c| substitute(c, name, with)),
    }
}

impl Skolemizer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn contains_quantifier(e: &Expr) -> bool {
        e.any_subterm(&|x| matches!(x, Expr::ForAll(_, _) | Expr::Exists(_, _)))
    }

    /// NNF + skolemisation of `e`. Returns the new formula and the skolem symbols created
    /// (name, signature) that the caller must declare.
    pub fn run(&mut self, e: &Expr) -> (Expr, Vec<(String, Type)>) {
        let mut declared = Vec::new();
        let out = self.go(e, true, &mut Vec::new(), &mut declared);
        (out, declared)
    }

    /// `universals`: the universally quantified variables in scope (skolem function arguments).
    fn go(
        &mut self,
        e: &Expr,
        positive: bool,
        universals: &mut Vec<(String, Type)>,
        declared: &mut Vec<(String, Type)>,
    ) -> Expr {
        if !Self::contains_quantifier(e) {
            return if positive { e.clone() } else { not(e.clone()) };
        }
        match e {
            Expr::Not(a) => self.go(a, !positive, universals, declared),
            Expr::And(args) | Expr::Or(args) => {
                let parts: Vec<Expr> = args
                    .iter()
                    .map(|a| self.go(a, positive, universals, declared))
                    .collect();
                // De Morgan: the connective flips under negation.
                if matches!(e, Expr::And(_)) == positive {
                    Expr::And(parts)
                } else {
                    Expr::Or(parts)
                }
            }
            Expr::Implies(a, b) => {
                let na = self.go(a, !positive, universals, declared);
                let pb = self.go(b, positive, universals, declared);
                if positive {
                    Expr::Or(vec![na, pb])
                } else {
                    Expr::And(vec![na, pb])
                }
            }
            Expr::Ite(c, t, f) if t.get_type() == Type::Bool || f.get_type() == Type::Bool => {
                // (c /\ t) \/ (!c /\ f), in either polarity
                let build = |this: &mut Self,
                             positive: bool,
                             universals: &mut Vec<(String, Type)>,
                             declared: &mut Vec<(String, Type)>| {
                    let (cp, cn) = (
                        this.go(c, true, universals, declared),
                        this.go(c, false, universals, declared),
                    );
                    let (tp, fp) = (
                        this.go(t, positive, universals, declared),
                        this.go(f, positive, universals, declared),
                    );
                    if positive {
                        Expr::Or(vec![Expr::And(vec![cp, tp]), Expr::And(vec![cn, fp])])
                    } else {
                        Expr::And(vec![Expr::Or(vec![cn, tp]), Expr::Or(vec![cp, fp])])
                    }
                };
                build(self, positive, universals, declared)
            }
            Expr::Eq(a, b) if a.get_type() == Type::Bool && b.get_type() == Type::Bool => {
                let (ap, an) = (
                    self.go(a, true, universals, declared),
                    self.go(a, false, universals, declared),
                );
                let (bp, bn) = (
                    self.go(b, true, universals, declared),
                    self.go(b, false, universals, declared),
                );
                if positive {
                    Expr::Or(vec![Expr::And(vec![ap, bp]), Expr::And(vec![an, bn])])
                } else {
                    Expr::Or(vec![Expr::And(vec![ap, bn]), Expr::And(vec![an, bp])])
                }
            }
            Expr::ForAll(vars, body) | Expr::Exists(vars, body) => {
                let existential = matches!(e, Expr::Exists(_, _)) == positive;
                if existential {
                    // Skolemise: each bound variable becomes a constant / function of the
                    // enclosing universals.
                    let mut body = (**body).clone();
                    for (v, ty) in vars {
                        let name = format!("__sk_{}", self.fresh);
                        self.fresh += 1;
                        let term = if universals.is_empty() {
                            declared.push((name.clone(), ty.clone()));
                            Expr::Var(name, ty.clone())
                        } else {
                            let sig = Type::Fn(
                                universals.iter().map(|(_, t)| t.clone()).collect(),
                                Box::new(ty.clone()),
                            );
                            declared.push((name.clone(), sig));
                            Expr::App(
                                name,
                                universals
                                    .iter()
                                    .map(|(n, t)| Expr::Var(n.clone(), t.clone()))
                                    .collect(),
                            )
                        };
                        body = substitute(&body, v, &term);
                    }
                    self.go(&body, positive, universals, declared)
                } else {
                    let depth = universals.len();
                    universals.extend(vars.iter().cloned());
                    let inner = self.go(body, positive, universals, declared);
                    universals.truncate(depth);
                    Expr::ForAll(vars.clone(), Box::new(inner))
                }
            }
            // A quantifier inside a term position (an argument of an atom) is not supported.
            _ => {
                if positive {
                    e.clone()
                } else {
                    not(e.clone())
                }
            }
        }
    }
}
