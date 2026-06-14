// SPDX-License-Identifier: MIT OR Apache-2.0
// Simplex termination via lexicographic ε-perturbation.
//
// The feasibility Simplex cycled on δ-pure degenerate systems (all variables free, multiple
// strict bounds active at the same rational point), returning Unknown instead of a verdict —
// e.g. `x>y ∧ y>z ∧ z>x` or `x+2y>4 ∧ 2x+y>4 ∧ x+y<2`. Bland's rule alone does not break that
// degeneracy. A lexicographic perturbation of every bound by an independent infinitesimal
// ε ≪ δ (DeltaRational's third level) makes each landing point unique and termination
// unconditional, while preserving SAT/UNSAT in the limit ε→0. These tests pin the verdicts
// AND fuzz-prove that no small LRA system returns Unknown.

use rz3::Rz3Solver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;

fn rv(n: &str) -> Expr { Expr::Var(n.into(), Type::Real) }
fn add(a: Expr, b: Expr) -> Expr { Expr::Add(vec![a, b]) }
fn mul(c: i64, v: &str) -> Expr { Expr::Mul(vec![Expr::Int(c), rv(v)]) }
fn gt(a: Expr, b: Expr) -> Expr { Expr::Gt(Box::new(a), Box::new(b)) }
fn lt(a: Expr, b: Expr) -> Expr { Expr::Lt(Box::new(a), Box::new(b)) }
fn i(n: i64) -> Expr { Expr::Int(n) }

#[test]
fn multirow_nondl_unsat_terminates() {
    // x+2y>4 ∧ 2x+y>4 ∧ x+y<2 : sum of first two ⇒ x+y>8/3>2, contradicts x+y<2. UNSAT.
    // Not same-form, not difference-logic, all vars free → must go through the Simplex.
    let mut s = Rz3Solver::new();
    s.assert(&gt(add(rv("x"), mul(2, "y")), i(4)));
    s.assert(&gt(add(mul(2, "x"), rv("y")), i(4)));
    s.assert(&lt(add(rv("x"), rv("y")), i(2)));
    assert!(matches!(s.check(), SolverResult::Unsat), "must be UNSAT, not Unknown");
}

#[test]
fn multirow_nondl_sat_terminates() {
    // x+2y>4 ∧ x+y<10 → SAT (soundness guard: perturbation must not fabricate UNSAT).
    let mut s = Rz3Solver::new();
    s.assert(&gt(add(rv("x"), mul(2, "y")), i(4)));
    s.assert(&lt(add(rv("x"), rv("y")), i(10)));
    assert!(matches!(s.check(), SolverResult::Sat), "must be SAT");
}

#[test]
fn pinned_equality_with_disequality_still_unsat() {
    // x==1 ∧ x≠1 → UNSAT. Guards that the perturbation does not un-pin equalities for ≠ checks.
    let mut s = Rz3Solver::new();
    s.assert(&Expr::Eq(Box::new(rv("x")), Box::new(i(1))));
    s.assert(&Expr::Not(Box::new(Expr::Eq(Box::new(rv("x")), Box::new(i(1))))));
    assert!(matches!(s.check(), SolverResult::Unsat), "x==1 ∧ x≠1 must be UNSAT");
}

// ─────────────────── Fuzz: no small LRA system returns Unknown ───────────────────

// Deterministic LCG (seeded) — rz3 forbids unseeded rand; the test owns its randomness.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 >> 33 }
    fn range(&mut self, lo: i64, hi: i64) -> i64 { lo + (self.next() as i64).rem_euclid(hi - lo + 1) }
}

#[test]
fn fuzz_no_unknown_on_small_systems() {
    let vars = ["x", "y", "z", "w"];
    let mut rng = Lcg(0xC0FFEE123);
    let mut sat = 0;
    let mut unsat = 0;
    for _ in 0..400 {
        let mut s = Rz3Solver::new();
        let nc = rng.range(2, 6); // 2..=6 constraints
        for _ in 0..nc {
            // random linear form Σ cᵢ·vᵢ over 1..=3 vars, coeffs in [-3,3]\{0}
            let nv = rng.range(1, 3) as usize;
            let mut form: Option<Expr> = None;
            for _ in 0..nv {
                let v = vars[rng.range(0, 3) as usize];
                let mut c = rng.range(-3, 3); if c == 0 { c = 1; }
                let term = mul(c, v);
                form = Some(match form { None => term, Some(f) => add(f, term) });
            }
            let form = form.unwrap();
            let bound = i(rng.range(-5, 5));
            let constraint = if rng.range(0, 1) == 0 { gt(form, bound) } else { lt(form, bound) };
            s.assert(&constraint);
        }
        match s.check() {
            SolverResult::Sat => sat += 1,
            SolverResult::Unsat => unsat += 1,
            SolverResult::Unknown => panic!("fuzz: a small LRA system returned Unknown — non-termination"),
        }
    }
    // Sanity: the corpus must exercise both verdicts (not all trivially one-sided).
    assert!(sat > 0 && unsat > 0, "fuzz corpus degenerate: sat={sat} unsat={unsat}");
    eprintln!("fuzz OK: {sat} SAT, {unsat} UNSAT, 0 Unknown over 400 random systems");
}
