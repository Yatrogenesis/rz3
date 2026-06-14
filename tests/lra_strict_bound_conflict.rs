// SPDX-License-Identifier: MIT OR Apache-2.0
// Regression tests for strict-bound infeasibility on a single linear form.
//
// Each asserted constraint allocates a fresh slack, so `x>0` and `x<0` produce two
// distinct slacks over the identical row `{x:1}` with `lower 0 (strict)` and
// `upper 0 (strict)`. Before the fix, the feasibility Simplex oscillated between those
// slacks and exhausted its pivot budget, returning `Unknown` instead of `Unsat`
// (surfaced first through lpm-rz3's smoke tests). `detect_row_bound_conflict` now
// catches the same-form contradiction up front. These tests pin the verdict at the
// solver level so future regressions are isolated to r-z3, not the bridge.

use rz3::Rz3Solver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;

fn int(n: i64) -> Expr { Expr::Int(n) }
fn ivar(name: &str) -> Expr { Expr::Var(name.to_string(), Type::Int) }
fn rvar(name: &str) -> Expr { Expr::Var(name.to_string(), Type::Real) }
fn real(numer: i64, scale: u32) -> Expr { Expr::Real(numer, scale) }

#[test]
fn strict_lower_and_upper_at_same_point_is_unsat() {
    // x > 0 ∧ x < 0  → UNSAT (empty open interval (0,0))
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(int(0))));
    s.assert(&Expr::Lt(Box::new(ivar("x")), Box::new(int(0))));
    assert!(matches!(s.check(), SolverResult::Unsat), "x>0 ∧ x<0 must be Unsat");
}

#[test]
fn real_crossing_strict_bounds_is_unsat() {
    // dose > 2.5 ∧ dose < 3.0 ∧ dose > 4.0  → UNSAT (lower 4.0 exceeds upper 3.0)
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(rvar("dose")), Box::new(real(25, 1))));
    s.assert(&Expr::Lt(Box::new(rvar("dose")), Box::new(real(30, 1))));
    s.assert(&Expr::Gt(Box::new(rvar("dose")), Box::new(real(40, 1))));
    assert!(matches!(s.check(), SolverResult::Unsat), "crossing real bounds must be Unsat");
}

#[test]
fn eq_then_strict_above_is_unsat() {
    // x == 5 ∧ x > 5  → UNSAT
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Eq(Box::new(ivar("x")), Box::new(int(5))));
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(int(5))));
    assert!(matches!(s.check(), SolverResult::Unsat), "x==5 ∧ x>5 must be Unsat");
}

// --- Soundness guard: the fix must NOT turn satisfiable systems into Unsat ---

#[test]
fn open_interval_with_room_is_sat() {
    // x > 0 ∧ x < 100  → SAT
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(int(0))));
    s.assert(&Expr::Lt(Box::new(ivar("x")), Box::new(int(100))));
    assert!(matches!(s.check(), SolverResult::Sat), "x>0 ∧ x<100 must be Sat");
}

#[test]
fn equal_nonstrict_bounds_pin_a_point_sat() {
    // x == 5  → SAT (lower 5 ∧ upper 5, both non-strict)
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Eq(Box::new(ivar("x")), Box::new(int(5))));
    assert!(matches!(s.check(), SolverResult::Sat), "x==5 must be Sat");
}

#[test]
fn real_open_interval_is_sat() {
    // dose > 2.5 ∧ dose < 3.0  → SAT
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(rvar("dose")), Box::new(real(25, 1))));
    s.assert(&Expr::Lt(Box::new(rvar("dose")), Box::new(real(30, 1))));
    assert!(matches!(s.check(), SolverResult::Sat), "dose∈(2.5,3.0) must be Sat");
}

// --- Canonical-form generalization: proportional and sign-variant forms ---

#[test]
fn proportional_forms_conflict_is_unsat() {
    // 2x>0 ∧ x<0 → UNSAT (rows {x:2} and {x:1} share canonical form {x:1})
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(Expr::Mul(vec![int(2), ivar("x")])), Box::new(int(0))));
    s.assert(&Expr::Lt(Box::new(ivar("x")), Box::new(int(0))));
    assert!(matches!(s.check(), SolverResult::Unsat), "2x>0 ∧ x<0 must be Unsat");
}

#[test]
fn sign_variant_forms_conflict_is_unsat() {
    // x>y ∧ y>x → UNSAT (rows {x:1,y:-1} and {x:-1,y:1} canonicalize to the same form)
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(ivar("y"))));
    s.assert(&Expr::Gt(Box::new(ivar("y")), Box::new(ivar("x"))));
    assert!(matches!(s.check(), SolverResult::Unsat), "x>y ∧ y>x must be Unsat");
}

// --- Soundness guards for canonical/sign-flip: must NOT become false UNSAT ---

#[test]
fn proportional_compatible_is_sat() {
    // 2x>0 ∧ x>-5 → SAT (canonical merge {x:1}, two lowers, no conflict)
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(Expr::Mul(vec![int(2), ivar("x")])), Box::new(int(0))));
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(int(-5))));
    assert!(matches!(s.check(), SolverResult::Sat), "2x>0 ∧ x>-5 must be Sat");
}

#[test]
fn sign_variant_compatible_interval_is_sat() {
    // x>y ∧ x<y+10  ≡  x-y ∈ (0,10) → SAT (canonical {x:1,y:-1}: lower 0, upper 10)
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(ivar("y"))));
    // x < y + 10  →  x - y < 10
    let y_plus_10 = Expr::Add(vec![ivar("y"), int(10)]);
    s.assert(&Expr::Lt(Box::new(ivar("x")), Box::new(y_plus_10)));
    assert!(matches!(s.check(), SolverResult::Sat), "x>y ∧ x<y+10 must be Sat");
}

#[test]
fn determinism_unsat_verdict_stable() {
    // The verdict must be identical across repeated independent solves (N=30).
    for _ in 0..30 {
        let mut s = Rz3Solver::new();
        s.assert(&Expr::Gt(Box::new(ivar("x")), Box::new(int(0))));
        s.assert(&Expr::Lt(Box::new(ivar("x")), Box::new(int(0))));
        assert!(matches!(s.check(), SolverResult::Unsat));
    }
}
