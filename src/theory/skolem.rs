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

#[cfg(test)]
mod tests {
    use super::*;

    fn b(e: Expr) -> Box<Expr> {
        Box::new(e)
    }
    fn iv(n: &str) -> Expr {
        Expr::Var(n.to_string(), Type::Int)
    }
    fn bv(n: &str) -> Expr {
        Expr::Var(n.to_string(), Type::Bool)
    }
    fn gt0(n: &str) -> Expr {
        Expr::Gt(b(iv(n)), b(Expr::Int(0)))
    }
    fn exists(v: &str, body: Expr) -> Expr {
        Expr::Exists(vec![(v.to_string(), Type::Int)], b(body))
    }
    fn forall(v: &str, body: Expr) -> Expr {
        Expr::ForAll(vec![(v.to_string(), Type::Int)], b(body))
    }
    fn sk(i: usize) -> Expr {
        Expr::Var(format!("__sk_{i}"), Type::Int)
    }
    fn gt_sk(i: usize) -> Expr {
        Expr::Gt(b(sk(i)), b(Expr::Int(0)))
    }
    fn not(e: Expr) -> Expr {
        Expr::Not(b(e))
    }
    fn run(e: &Expr) -> (Expr, Vec<(String, Type)>) {
        Skolemizer::new().run(e)
    }

    #[test]
    fn substitute_respects_shadowing_and_kind() {
        let with = Expr::Int(7);
        assert_eq!(
            substitute(&gt0("x"), "x", &with),
            Expr::Gt(b(with.clone()), b(Expr::Int(0)))
        );
        assert_eq!(substitute(&gt0("y"), "x", &with), gt0("y"));
        // Bound occurrence: untouched.
        let shadow = forall("x", gt0("x"));
        assert_eq!(substitute(&shadow, "x", &with), shadow);
        // Free occurrence under a different binder: replaced, binder kind kept.
        let inner = Expr::Gt(b(iv("x")), b(iv("z")));
        assert_eq!(
            substitute(&forall("z", inner.clone()), "x", &with),
            forall("z", Expr::Gt(b(with.clone()), b(iv("z"))))
        );
        assert_eq!(
            substitute(&exists("z", inner), "x", &with),
            exists("z", Expr::Gt(b(with), b(iv("z"))))
        );
    }

    #[test]
    fn detects_quantifiers_anywhere() {
        assert!(!Skolemizer::contains_quantifier(&gt0("x")));
        assert!(Skolemizer::contains_quantifier(&forall("x", gt0("x"))));
        assert!(Skolemizer::contains_quantifier(&Expr::And(vec![
            bv("p"),
            not(exists("x", gt0("x")))
        ])));
    }

    #[test]
    fn quantifier_free_formulas_only_get_their_polarity() {
        let e = Expr::And(vec![bv("p"), bv("q")]);
        assert_eq!(run(&e), (e.clone(), vec![]));
    }

    #[test]
    fn existential_becomes_a_constant() {
        let (out, decl) = run(&exists("x", gt0("x")));
        assert_eq!(out, gt_sk(0));
        assert_eq!(decl, vec![("__sk_0".to_string(), Type::Int)]);
        // Under negation an existential is a universal, which stays.
        let (out, decl) = run(&not(exists("x", gt0("x"))));
        assert_eq!(out, forall("x", not(gt0("x"))));
        assert!(decl.is_empty());
        // A positive universal stays; a negated universal is skolemised.
        let (out, decl) = run(&forall("x", gt0("x")));
        assert_eq!(out, forall("x", gt0("x")));
        assert!(decl.is_empty());
        let (out, decl) = run(&not(forall("x", gt0("x"))));
        assert_eq!(out, not(gt_sk(0)));
        assert_eq!(decl.len(), 1);
    }

    #[test]
    fn fresh_names_are_consecutive() {
        let e = Expr::Exists(
            vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
            b(Expr::Gt(b(iv("x")), b(iv("y")))),
        );
        let (out, decl) = run(&e);
        assert_eq!(out, Expr::Gt(b(sk(0)), b(sk(1))));
        assert_eq!(
            decl,
            vec![
                ("__sk_0".to_string(), Type::Int),
                ("__sk_1".to_string(), Type::Int)
            ]
        );
        // The counter persists across calls of one skolemizer.
        let mut s = Skolemizer::new();
        s.run(&exists("x", gt0("x")));
        let (out, _) = s.run(&exists("x", gt0("x")));
        assert_eq!(out, gt_sk(1));
    }

    #[test]
    fn existential_under_a_universal_becomes_a_function() {
        let body = Expr::Gt(b(iv("x")), b(iv("y")));
        let (out, decl) = run(&forall("y", exists("x", body)));
        let app = Expr::App("__sk_0".to_string(), vec![iv("y")]);
        assert_eq!(out, forall("y", Expr::Gt(b(app), b(iv("y")))));
        assert_eq!(
            decl,
            vec![(
                "__sk_0".to_string(),
                Type::Fn(vec![Type::Int], Box::new(Type::Int))
            )]
        );
        // The universal goes out of scope afterwards: a sibling existential is a constant.
        let both = Expr::And(vec![forall("y", gt0("y")), exists("x", gt0("x"))]);
        let (out, decl) = run(&both);
        assert_eq!(out, Expr::And(vec![forall("y", gt0("y")), gt_sk(0)]));
        assert_eq!(decl, vec![("__sk_0".to_string(), Type::Int)]);
    }

    #[test]
    fn de_morgan_flips_the_connective() {
        let q = bv("q");
        let and = Expr::And(vec![exists("x", gt0("x")), q.clone()]);
        assert_eq!(run(&and).0, Expr::And(vec![gt_sk(0), q.clone()]));
        assert_eq!(
            run(&not(and)).0,
            Expr::Or(vec![forall("x", not(gt0("x"))), not(q.clone())])
        );
        let or = Expr::Or(vec![exists("x", gt0("x")), q.clone()]);
        assert_eq!(run(&or).0, Expr::Or(vec![gt_sk(0), q.clone()]));
        assert_eq!(
            run(&not(or)).0,
            Expr::And(vec![forall("x", not(gt0("x"))), not(q)])
        );
    }

    #[test]
    fn implication_is_expanded_by_polarity() {
        let q = bv("q");
        let imp = Expr::Implies(b(exists("x", gt0("x"))), b(q.clone()));
        // (E x. P) -> q  ==  (A x. !P) \/ q
        assert_eq!(
            run(&imp).0,
            Expr::Or(vec![forall("x", not(gt0("x"))), q.clone()])
        );
        // !((A x. P) -> q)  ==  (A x. P) /\ !q
        let imp = Expr::Implies(b(forall("x", gt0("x"))), b(q.clone()));
        assert_eq!(
            run(&not(imp)).0,
            Expr::And(vec![forall("x", gt0("x")), not(q)])
        );
    }

    #[test]
    fn boolean_ite_is_expanded_in_both_polarities() {
        let (c, q) = (bv("c"), bv("q"));
        let ite = Expr::Ite(b(c.clone()), b(exists("x", gt0("x"))), b(q.clone()));
        assert_eq!(
            run(&ite).0,
            Expr::Or(vec![
                Expr::And(vec![c.clone(), gt_sk(0)]),
                Expr::And(vec![not(c.clone()), q.clone()])
            ])
        );
        assert_eq!(
            run(&not(ite)).0,
            Expr::And(vec![
                Expr::Or(vec![not(c.clone()), forall("x", not(gt0("x")))]),
                Expr::Or(vec![c.clone(), not(q.clone())])
            ])
        );
        // Only one branch Boolean (then): still expanded.
        let ite = Expr::Ite(b(c.clone()), b(forall("x", gt0("x"))), b(iv("n")));
        assert!(matches!(run(&ite).0, Expr::Or(_)));
        // Only one branch Boolean (else): still expanded.
        let ite = Expr::Ite(b(c), b(iv("n")), b(forall("x", gt0("x"))));
        assert!(matches!(run(&ite).0, Expr::Or(_)));
    }

    #[test]
    fn boolean_equivalence_is_expanded_in_both_polarities() {
        let (p, q) = (forall("x", gt0("x")), bv("q"));
        let e = Expr::Eq(b(p.clone()), b(q.clone()));
        assert_eq!(
            run(&e).0,
            Expr::Or(vec![
                Expr::And(vec![p.clone(), q.clone()]),
                Expr::And(vec![not(gt_sk(0).clone()), not(q.clone())]),
            ])
        );
        assert_eq!(
            run(&not(e)).0,
            Expr::Or(vec![
                Expr::And(vec![p, not(q.clone())]),
                Expr::And(vec![not(gt_sk(0)), q]),
            ])
        );
    }

    #[test]
    fn mixed_sort_equality_is_not_a_boolean_equivalence() {
        // Ill-sorted on purpose: the guard requires BOTH sides Boolean.
        let e = Expr::Eq(b(forall("x", gt0("x"))), b(iv("n")));
        assert_eq!(run(&e).0, e);
        let e = Expr::Eq(b(iv("n")), b(forall("x", gt0("x"))));
        assert_eq!(run(&e).0, e);
    }
}
