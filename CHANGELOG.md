# Changelog

All notable changes to `rz3` are documented here. Format based on
[Keep a Changelog](https://keepachangelog.com/); this project follows semantic versioning.

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
