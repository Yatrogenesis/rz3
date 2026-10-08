# Changelog

All notable changes to `rz3` are documented here. Format based on
[Keep a Changelog](https://keepachangelog.com/); this project follows semantic versioning.

## [Unreleased]

Soundness fixes found by a 120-case differential pilot against Z3 5.1.0
(`rz3` 0.1.4 answered `sat` on 56 of 60 `unsat` controls and could answer
`unsat` on satisfiable inputs). Root causes were in the SMT-LIB front end and in
conflict handling, not in the theory algorithms themselves. Behaviour change:
inputs RZ3 cannot interpret now produce an error or `unknown`, never a verdict.

### Added
- Incremental linearization for nonlinear real/integer arithmetic (sign, tangent, McCormick
  and monotonicity lemmas); `sat` only when the exact evaluator confirms the model.
- Floating point: `Float16/32/64`, `(_ +oo|-oo|+zero|-zero|NaN e s)`, IEEE comparisons,
  `to_fp` from a real literal or a bit pattern, `fp.min`/`fp.max`; terms that cannot be
  evaluated (free FP variables) give `unknown`.
- Models are printed in standard SMT-LIB syntax (`(- 1)`, `1.0`, `(/ 1.0 2.0)`).
- Regression batteries: strings fail closed (145 scripts cross-checked with Z3), 107+ front-end
  rows cross-checked with Z3, unit tests for the congruence closure and the fast rationals
  derived from a mutation run (`cargo-mutants`).

### Fixed
- **`div`/`mod` by zero:** `(mod x 0)` was rewritten to `x`, refuting satisfiable problems
  (found with yinyang/typefuzz). The standard leaves it unspecified; RZ3 now answers `unknown`.
- **Front end:** operators it did not know (`-`, `distinct`, `=>`, `xor`, every
  `bv*`, ...) were silently turned into uninterpreted applications, so `(- a b)`
  became a free variable. They are now translated; anything unsupported is a
  parse error. `#x..` literals were lexed as integers; numerals over 64 bits and
  unknown commands used to end the script silently (and answer `sat` for the
  prefix); `define-fun` bodies were discarded; `let`/`declare-const` were missing;
  chainable `= <= < >= >` kept only the first two arguments.
- **SAT core:** clauses were added on top of a stale assignment after `solve()`,
  `backtrack` dropped pending units, unassigned variables were not returned to the
  decision heap, and learnt clauses were sorted, breaking the watch invariant.
  `new_var` in the bit-blaster re-enabled an already-inconsistent solver.
- **Tactics:** `SolveEqs` lost equations (`x=1 /\ x=2`, cyclic definitions).
- **Bit-vectors:** unsupported operators produced an empty vector (equality then
  held trivially); `bvmul`, `bvor`, `bvxor`, `bvnot`, `bvsub`, shifts, extract,
  concat and the four comparisons are now encoded; anything else makes the
  verdict `unknown`.
- **Arithmetic:** `ite` is lifted to propositional structure; division by a
  constant and unary minus are exact; `Int` variables are enforced by bound
  normalisation and branch-and-bound; real/decimal constants no longer disappear
  from the nonlinear check; abstracted terms never support a `sat` verdict.
- **Conflict explanations:** EUF and LRA reported partial cores, so learned
  clauses could exclude satisfiable assignments (spurious `unsat`). Cores are now
  minimal-by-deletion (EUF) or conservative (LRA).
- **Uninterpreted functions:** applications are Ackermann-reduced, so congruence
  holds over arithmetic and bit-vector arguments.

- **Constant folding:** `i64` overflow in `+`, `*` and `-` wrapped around and made
  `(> (+ 9223372036854775807 1) 0)` unsatisfiable; folding is now checked and an
  overflowing term is left to the exact arithmetic theory.

### Verification
Release binary `cc4cbd34b76a6ea4` (this tree): pilot 840/840 correct, 0 non-repeatable;
93 tests pass; `clippy -D warnings` and `fmt --check` clean; determinism n=30 gives one
hash over a 500-script corpus; 6,500 random scripts (single and incremental
`check-sat`/`push`/`pop`, bit-vectors of width 1..64) with 0 sat/unsat disagreements
against Z3 5.1.0. Earlier snapshots of the same code (before the overflow fix and the
second certification layer) were fuzzed with 22,000 further scripts and also showed 0.
Known limits: 9 of the 6,500 scripts timed out after 20 s (wide bit-vector
multiplication; Z3 answers in ~0.1 s), and RZ3 never decides floating-point, array,
string or quantified inputs it was not tested on. Pre-fix timings are not comparable.

### Added
- `rz3::driver::check_script`, `rz3::eval` (exact model evaluation used to certify
  every `sat`), `Parser::strict`/`Parser::error`, `Command::Skipped`.
- `tests/frontend_soundness.rs`, `tests/sat_fuzz_vs_bruteforce.rs`,
  `scripts/differential_fuzz.py` (random scripts, rz3 vs z3, zero tolerated
  sat/unsat disagreements).

## [0.1.4] — 2026-07-30

Soundness and hardening fixes for theory solvers that could previously return
`Sat` outside their decidable fragment. No API breakage; the sound theories
(LRA / EUF / DL / array / fp) are unchanged and their tests still pass.

### Fixed
- **Quantifier (RZ3-2):** the top-level solver could return `Sat` for a formula
  with a live universal (`ForAll`) assertion — `QuantifierSolver::check()` was
  `{ true }` and its result was never consulted. The solver now returns
  `Unknown` when a universal remains after E-matching/MBQI reaches a lemma
  fixpoint. A fixpoint means "no counterexample found among the explored ground
  terms", not validity over the whole domain.
- **Nonlinear arithmetic (RZ3-1):** `check()` decided only one narrow conflict
  shape and otherwise let a `Sat` stand. Genuine nonlinear content (total
  degree ≥ 2) that the decidable shape-check cannot resolve now yields
  `Unknown` instead of an unverified `Sat`; no general nonlinear decision
  procedure is wired into `check()`.
- **Strings (RZ3-3):** `check()` verified only conflicting `str.len(s) = literal`
  equalities among its own length axioms; `StrConcat` / `StrContains` were not
  actually verified. Constraints mentioning those operations now yield `Unknown`.

### Added
- **Bit-vectors (RZ3-5):** `MAX_BV_WIDTH = 4096`. Bit-vector width was an
  unbounded `usize`; a single wide `BvConst` / `BitVec` (e.g. from untrusted
  SMT-LIB input) could drive `bit_blast` to emit one SAT variable and clause
  per bit without limit — an out-of-memory / denial-of-service vector,
  particularly on `wasm32`. `bit_blast` now refuses (asserts) above the cap
  rather than expanding unboundedly.

### Notes
- `RZ3-4` (further nonlinear / quantifier / string completeness) is reported,
  not addressed in this release.
- Callers must continue to handle `SolverResult::Unknown`. These fixes increase
  the cases in which it is returned, in exchange for no longer returning an
  unsound `Sat`.

## [0.1.3] — 2026-06-18

Crates.io documentation and release-hardening update.

### Changed
- Corrected package documentation to describe the current supported SMT scope honestly:
  `rz3` is not a drop-in replacement for Z3, several theories are partial, and callers must
  handle `SolverResult::Unknown`.
- Added crate-level docs for docs.rs.
- Declared `rust-version = "1.70"` and replaced newer standard-library APIs so the declared
  MSRV is enforced by clippy.
- Removed a dead test helper so `cargo clippy --all-targets -- -D warnings` passes.

## [0.1.2] — 2026-06-14

First public release. (Supersedes the never-published 0.1.0/0.1.1 tags. Zenodo
archival kept failing to load `CITATION.cff` because its `license` field is
multi-valued — Zenodo's deposition metadata expects a single license, so neither
the SPDX expression nor the SPDX list parsed. Switched to a native `.zenodo.json`
with a single-string license, which takes precedence over CFF. No solver code changed.)

### Solver
- DPLL(T) architecture: a deterministic CDCL SAT core driving a set of theory solvers.
- **Linear arithmetic (LRA/LIA): exact and deterministic.** Exact incremental Simplex
  (Dutertre–de Moura) over arbitrary-precision rationals; strict inequalities via a symbolic
  `δ` infinitesimal; lexicographic `ε`-perturbation and regression coverage for
  termination-sensitive cases. Some unresolved degenerate or disequality-heavy cases may return
  `Unknown`.
- Difference-logic fragment decided directly by negative-cycle detection (Bellman-Ford).
- Same-linear-form bound conflicts decided by a canonical pre-check.
- EUF (congruence closure), arrays (read-over-write); partial bit-vectors, strings,
  floating-point, quantifier instantiation and non-linear arithmetic.
- SMT-LIB 2.6 front-end (a subset of the standard).

### Guarantees
- **Exact**: arbitrary-precision rationals; no floating-point in the decision core.
- **Deterministic**: `n=30` bit-identical (SHA-256) harness; no `rand`, no parallelism in the
  decision path; ordered (`BTreeMap`/`BTreeSet`) collections; index-based tie-breaks.
- **Portable**: pure Rust, zero native dependencies, `wasm32`-deployable.

### License
- Dual-licensed under MIT OR Apache-2.0.
