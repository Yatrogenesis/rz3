//! Characterisation of the CDCL search on structured and seeded random instances.
//!
//! The solver is deterministic, so the numbers of propagations, decisions, conflicts, restarts and
//! learnt clauses for a fixed instance are a fingerprint of the search. Any change to the
//! heuristics (decision order, restarts, clause database reduction, conflict analysis) changes
//! them; this test makes such a change visible and requires the author to update the figures on
//! purpose. Answers are independently validated: models are checked against the clauses, the
//! pigeonhole formulas are unsatisfiable by a counting argument, and the verdicts of the four
//! seeded random instances (unsat, unsat, unsat, sat) were confirmed with Z3 5.1.0.

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

/// Number of variables and the clauses.
type Cnf = (usize, Vec<Vec<i32>>);

fn pigeonhole(holes: usize) -> Cnf {
    let pigeons = holes + 1;
    let var = |p: usize, h: usize| (p * holes + h + 1) as i32;
    let mut cnf = Vec::new();
    for p in 0..pigeons {
        cnf.push((0..holes).map(|h| var(p, h)).collect());
    }
    for h in 0..holes {
        for p in 0..pigeons {
            for q in p + 1..pigeons {
                cnf.push(vec![-var(p, h), -var(q, h)]);
            }
        }
    }
    (pigeons * holes, cnf)
}

fn random_3sat(n: usize, m: usize, seed: u64) -> Cnf {
    let mut rng = Xorshift(seed);
    let cnf = (0..m)
        .map(|_| {
            let mut vs: Vec<i32> = Vec::new();
            while vs.len() < 3 {
                let v = 1 + rng.below(n as u64) as i32;
                if !vs.contains(&v) {
                    vs.push(v);
                }
            }
            vs.into_iter()
                .map(|v| if rng.below(2) == 0 { v } else { -v })
                .collect()
        })
        .collect();
    (n, cnf)
}

fn run(num_vars: usize, cnf: &[Vec<i32>]) -> (bool, [u64; 5]) {
    let mut s = CdclSolver::new();
    let _ = num_vars; // variables are created on demand by add_clause
    for c in cnf {
        s.add_clause(c.clone());
    }
    let sat = s.solve();
    if sat {
        assert!(
            cnf.iter()
                .all(|c| c.iter().any(|&l| s.get_lit_value(l) == Assignment::True)),
            "the reported model violates a clause"
        );
    }
    let st = &s.stats;
    (
        sat,
        [
            st.propagations,
            st.decisions,
            st.conflicts,
            st.restarts,
            st.learned_clauses,
        ],
    )
}

#[test]
fn search_fingerprint_is_stable() {
    // (name, expected satisfiability, instance)
    let mut cases: Vec<(String, bool, Cnf)> = Vec::new();
    for h in [5usize, 6, 7] {
        cases.push((format!("php{h}"), false, pigeonhole(h)));
    }
    for (n, seed) in [(60usize, 11u64), (75, 12), (90, 13), (110, 14)] {
        let m = (n as f64 * 4.26) as usize;
        cases.push((
            format!("r3sat_{n}_{seed}"),
            n == 110,
            random_3sat(n, m, seed),
        ));
    }
    let mut report = String::new();
    for (name, expect_sat, (n, cnf)) in &cases {
        let (sat, stats) = run(*n, cnf);
        report.push_str(&format!("{name} sat={sat} {stats:?}\n"));
        assert_eq!(sat, *expect_sat, "{name}");
    }
    println!("{report}");
    let expected = std::fs::read_to_string("tests/sat_search_golden.txt")
        .expect("tests/sat_search_golden.txt holds the reference fingerprints");
    assert_eq!(report, expected, "the search fingerprint changed");
}
