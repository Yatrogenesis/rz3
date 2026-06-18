// SPDX-License-Identifier: MIT OR Apache-2.0
// Difference-Logic fragment: infeasibility of `±x ∓ y OP c` systems is a negative
// cycle in the constraint graph (Bellman-Ford), which the feasibility Simplex cannot
// see when all variables are free (it cycles → sound Unknown). A dedicated DL
// pre-check decides this fragment directly.
//
// Soundness is the whole game here: a false UNSAT is strictly worse than the prior
// sound Unknown. The SAT guards below are written FIRST and pin the failure modes —
// non-strict zero cycles (SAT), paths without cycles (SAT), and sums that must NOT
// become graph edges (SAT).

use rz3::ast::{Expr, Type};
use rz3::Rz3Solver;
use rz3::SolverResult;

fn iv(n: &str) -> Expr {
    Expr::Var(n.into(), Type::Int)
}
fn rv(n: &str) -> Expr {
    Expr::Var(n.into(), Type::Real)
}
fn gt(a: Expr, b: Expr) -> Expr {
    Expr::Gt(Box::new(a), Box::new(b))
}
fn ge(a: Expr, b: Expr) -> Expr {
    Expr::Ge(Box::new(a), Box::new(b))
}
fn i(n: i64) -> Expr {
    Expr::Int(n)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::Add(vec![a, b])
}
fn sub(a: Expr, b: Expr) -> Expr {
    Expr::Sub(vec![a, b])
}

// ───────────────────── SAT GUARDS (written first) ─────────────────────

#[test]
fn nonstrict_zero_cycle_is_sat() {
    // x≥y ∧ y≥z ∧ z≥x  → SAT  (x=y=z; zero-weight cycle, all non-strict)
    let mut s = Rz3Solver::new();
    s.assert(&ge(iv("x"), iv("y")));
    s.assert(&ge(iv("y"), iv("z")));
    s.assert(&ge(iv("z"), iv("x")));
    assert!(
        matches!(s.check(), SolverResult::Sat),
        "x≥y ∧ y≥z ∧ z≥x must be SAT"
    );
}

#[test]
fn strict_path_no_cycle_is_sat() {
    // x>y ∧ y>z  → SAT  (a path, not a cycle)
    let mut s = Rz3Solver::new();
    s.assert(&gt(iv("x"), iv("y")));
    s.assert(&gt(iv("y"), iv("z")));
    assert!(
        matches!(s.check(), SolverResult::Sat),
        "x>y ∧ y>z must be SAT"
    );
}

#[test]
fn sum_constraint_must_not_become_edge_sat() {
    // x+y>0 ∧ x>y  → SAT.  `x+y` is a SUM, not a difference; it must NOT be treated
    // as a DL edge (doing so would fabricate a false cycle/UNSAT).
    let mut s = Rz3Solver::new();
    s.assert(&gt(add(iv("x"), iv("y")), i(0)));
    s.assert(&gt(iv("x"), iv("y")));
    assert!(
        matches!(s.check(), SolverResult::Sat),
        "x+y>0 ∧ x>y must be SAT"
    );
}

#[test]
fn weighted_cycle_with_slack_is_sat() {
    // x−y>1 ∧ y−z>1 ∧ z−x>−3  → cycle weight sum = (>1)+(>1)+(>-3): x−y+y−z+z−x = 0,
    // and 1+1−3 = −1 < 0, so the constraints require 0 > −1 (true) → SAT (room to spare).
    let mut s = Rz3Solver::new();
    s.assert(&gt(sub(rv("x"), rv("y")), i(1)));
    s.assert(&gt(sub(rv("y"), rv("z")), i(1)));
    s.assert(&gt(sub(rv("z"), rv("x")), i(-3)));
    assert!(
        matches!(s.check(), SolverResult::Sat),
        "feasible weighted cycle must be SAT"
    );
}

// ───────────────────── UNSAT (the fragment we are closing) ─────────────────────

#[test]
fn strict_zero_cycle_is_unsat() {
    // x>y ∧ y>z ∧ z>x  → UNSAT  (zero-weight cycle with strict edges → 0 > 0)
    let mut s = Rz3Solver::new();
    s.assert(&gt(iv("x"), iv("y")));
    s.assert(&gt(iv("y"), iv("z")));
    s.assert(&gt(iv("z"), iv("x")));
    assert!(
        matches!(s.check(), SolverResult::Unsat),
        "x>y ∧ y>z ∧ z>x must be UNSAT"
    );
}

#[test]
fn two_var_strict_cycle_is_unsat() {
    // x>y ∧ y>x  → UNSAT (also caught by the canonical-row check; DL agrees)
    let mut s = Rz3Solver::new();
    s.assert(&gt(iv("x"), iv("y")));
    s.assert(&gt(iv("y"), iv("x")));
    assert!(
        matches!(s.check(), SolverResult::Unsat),
        "x>y ∧ y>x must be UNSAT"
    );
}

#[test]
fn weighted_negative_cycle_is_unsat() {
    // x−y>3 ∧ y−z>3 ∧ z−x>−5  → sum 3+3−5 = 1, requires 0 > 1 → UNSAT
    let mut s = Rz3Solver::new();
    s.assert(&gt(sub(rv("x"), rv("y")), i(3)));
    s.assert(&gt(sub(rv("y"), rv("z")), i(3)));
    s.assert(&gt(sub(rv("z"), rv("x")), i(-5)));
    assert!(
        matches!(s.check(), SolverResult::Unsat),
        "weighted negative cycle must be UNSAT"
    );
}

#[test]
fn four_var_cycle_is_unsat() {
    // a>b ∧ b>c ∧ c>d ∧ d>a → UNSAT (longer strict zero cycle)
    let mut s = Rz3Solver::new();
    s.assert(&gt(iv("a"), iv("b")));
    s.assert(&gt(iv("b"), iv("c")));
    s.assert(&gt(iv("c"), iv("d")));
    s.assert(&gt(iv("d"), iv("a")));
    assert!(
        matches!(s.check(), SolverResult::Unsat),
        "4-var strict cycle must be UNSAT"
    );
}

// --- Regression: extract_coeffs(Sub) must be real subtraction, not addition ---

#[test]
fn sub_is_real_subtraction_not_addition() {
    // x − y == 2 ∧ x == 5 ∧ y == 3  → SAT (5−3 = 2).
    // The old `Sub` extraction turned `x − y` into `x + y`, which would make this
    // 5+3 = 8 ≠ 2 → a false UNSAT. This pins subtraction of variables.
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Eq(Box::new(sub(iv("x"), iv("y"))), Box::new(i(2))));
    s.assert(&Expr::Eq(Box::new(iv("x")), Box::new(i(5))));
    s.assert(&Expr::Eq(Box::new(iv("y")), Box::new(i(3))));
    assert!(
        matches!(s.check(), SolverResult::Sat),
        "x−y==2 ∧ x==5 ∧ y==3 must be SAT"
    );
}

#[test]
fn determinism_dl_unsat_stable() {
    for _ in 0..30 {
        let mut s = Rz3Solver::new();
        s.assert(&gt(iv("x"), iv("y")));
        s.assert(&gt(iv("y"), iv("z")));
        s.assert(&gt(iv("z"), iv("x")));
        assert!(matches!(s.check(), SolverResult::Unsat));
    }
}
