# Changelog

All notable changes to `rz3` are documented here. Format based on
[Keep a Changelog](https://keepachangelog.com/); this project follows semantic versioning.

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
