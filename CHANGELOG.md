# Changelog

All notable changes to `rz3` are documented here. Format based on
[Keep a Changelog](https://keepachangelog.com/); this project follows semantic versioning.

## [0.1.0] — unreleased

First public release.

### Solver
- DPLL(T) architecture: a deterministic CDCL SAT core driving a set of theory solvers.
- **Linear arithmetic (LRA/LIA): complete and terminating.** Exact incremental Simplex
  (Dutertre–de Moura) over arbitrary-precision rationals; strict inequalities via a symbolic
  `δ` infinitesimal; **unconditional termination via a lexicographic `ε`-perturbation** — the
  feasibility Simplex never returns `Unknown` from cycling (verified by a randomized
  termination test over hundreds of independent systems).
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
