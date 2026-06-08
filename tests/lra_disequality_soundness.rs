// Oráculo de SOUNDNESS para desigualdades (≠) en LRA.
// (correctitud, no solo determinismo). Ver advisor 2026-06-07.

use rz3::ast::{Expr, Type};
use rz3::{Rz3Solver, SolverResult};

fn real(n: &str) -> Expr { Expr::Var(n.to_string(), Type::Real) }
fn ge(x: &Expr, k: i64) -> Expr { Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(k))) }
fn le(x: &Expr, k: i64) -> Expr { Expr::Le(Box::new(x.clone()), Box::new(Expr::Int(k))) }
fn ne(x: &Expr, k: i64) -> Expr {
    Expr::Not(Box::new(Expr::Eq(Box::new(x.clone()), Box::new(Expr::Int(k)))))
}

/// ANCLA DE VERIFICACIÓN: x∈[0,2] ∧ x≠0 -> SAT (x puede repararse a 1).
/// Antes del fix: el código devuelve UNSAT (var fresca = 0, cota factible,
/// disequality ve 0==0 -> false). Eso es la INSOUNDNESS que se repara.
#[test]
fn diseq_sat_can_repair() {
    let mut s = Rz3Solver::new();
    let x = real("x");
    s.assert(&ge(&x, 0));
    s.assert(&le(&x, 2));
    s.assert(&ne(&x, 0));
    assert!(matches!(s.check(), SolverResult::Sat), "x∈[0,2] ∧ x≠0 debe ser SAT");
}

/// GENUINO UNSAT (el fix NO debe romperlo): x=1 congelado ∧ x≠1 -> UNSAT.
#[test]
fn diseq_genuine_unsat_frozen() {
    let mut s = Rz3Solver::new();
    let x = real("x");
    s.assert(&ge(&x, 1));
    s.assert(&le(&x, 1));
    s.assert(&ne(&x, 1));
    assert!(matches!(s.check(), SolverResult::Unsat), "x=1 ∧ x≠1 debe ser UNSAT");
}

/// ORÁCULO δ-RACIONAL: x>0 ∧ x<1/1000000 -> SAT exacto.
/// Antes del fix: la perturbación fija 1/1000000 hacía que el solver eligiera x=1/1000000
/// y violara la cota superior estricta, devolviendo UNSAT incorrecto.
#[test]
fn strict_tight_interval_needs_delta_rational() {
    let mut s = Rz3Solver::new();
    let x = real("x");
    s.assert(&Expr::Gt(Box::new(x.clone()), Box::new(Expr::Int(0))));
    s.assert(&Expr::Lt(Box::new(x.clone()), Box::new(Expr::Real(1, 6)))); // 1/10^6
    assert!(matches!(s.check(), SolverResult::Sat), "intervalo estrecho exacto debe ser SAT");
}
