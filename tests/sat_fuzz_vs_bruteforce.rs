//! Differential test of the CDCL core against exhaustive enumeration, including the
//! incremental pattern the SMT loop uses (solve, add clauses, solve again).

use rz3::sat::{Assignment, CdclSolver};

struct Xorshift(u64);
impl Xorshift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn brute_force(num_vars: usize, clauses: &[Vec<i32>]) -> bool {
    (0..(1u32 << num_vars)).any(|mask| {
        clauses.iter().all(|c| {
            c.iter().any(|&l| {
                let v = (l.unsigned_abs() as usize) - 1;
                let val = (mask >> v) & 1 == 1;
                if l > 0 {
                    val
                } else {
                    !val
                }
            })
        })
    })
}

fn model_satisfies(solver: &CdclSolver, clauses: &[Vec<i32>]) -> bool {
    clauses.iter().all(|c| {
        c.iter()
            .any(|&l| solver.get_lit_value(l) == Assignment::True)
    })
}

fn random_clause(rng: &mut Xorshift, num_vars: u64) -> Vec<i32> {
    let len = 1 + rng.below(4) as usize;
    (0..len)
        .map(|_| {
            let v = 1 + rng.below(num_vars) as i32;
            if rng.below(2) == 0 {
                v
            } else {
                -v
            }
        })
        .collect()
}

#[test]
fn incremental_cdcl_matches_exhaustive_search() {
    let mut rng = Xorshift(0x9E37_79B9_7F4A_7C15);
    let mut disagreements = Vec::new();
    for case in 0..3000 {
        let num_vars = 3 + rng.below(6) as usize; // 3..=8
        let rounds = 1 + rng.below(5);
        let mut solver = CdclSolver::new();
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        for round in 0..rounds {
            let batch = 1 + rng.below(7);
            for _ in 0..batch {
                let clause = random_clause(&mut rng, num_vars as u64);
                clauses.push(clause.clone());
                let _ = solver.add_clause(clause);
            }
            let expected = brute_force(num_vars, &clauses);
            let got = solver.solve();
            if got != expected {
                disagreements.push(format!(
                    "case {case} round {round}: expected {expected}, got {got}, clauses {clauses:?}"
                ));
                break;
            }
            if got && !model_satisfies(&solver, &clauses) {
                // Unassigned variables are free; only assigned-false literals matter.
                let ok = clauses.iter().all(|c| {
                    c.iter()
                        .any(|&l| solver.get_lit_value(l) != Assignment::False)
                });
                if !ok {
                    disagreements.push(format!(
                        "case {case} round {round}: model violates a clause, clauses {clauses:?}"
                    ));
                    break;
                }
            }
            if !expected {
                break;
            }
        }
    }
    assert!(
        disagreements.is_empty(),
        "{} disagreement(s); first: {}",
        disagreements.len(),
        disagreements.first().cloned().unwrap_or_default()
    );
}
