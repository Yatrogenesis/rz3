# rz3 — a deterministic, exact-rational SMT solver in pure Rust

`rz3` is an SMT (Satisfiability Modulo Theories) solver written entirely in safe Rust, with
**no C/C++ dependencies**. It is built around three properties that are uncommon together:

- **Exact** — arithmetic is computed over arbitrary-precision rationals (`num-rational` /
  `num-bigint`). There is no floating-point in the decision core, so there are no rounding
  artifacts and no false verdicts from numeric error.
- **Deterministic** — the same input yields the *same* result on every run (verified by an
  `n=30` bit-identical harness). There is no `rand`, no wall-clock-dependent heuristic, and
  no timeout-induced nondeterminism.
- **Portable** — pure Rust with zero native dependencies, so it compiles to `wasm32` and
  embeds without FFI. This is the niche `rz3` was built for: SMT where a C++ solver cannot go.

It is not a drop-in replacement for Z3 — see **[Scope and limitations](#scope-and-limitations)**.

## What it does

`rz3` is a lazy SMT solver (DPLL(T)): a CDCL SAT core drives a set of theory solvers.

| Layer | Status |
|---|---|
| CDCL SAT core (deterministic VSIDS, restarts) | stable |
| **Linear arithmetic (LRA/LIA)** — exact Simplex, δ-rational strict bounds, lexicographic anti-cycling | **complete & terminating** |
| Difference logic (negative-cycle detection) | complete |
| Uninterpreted functions + equality (EUF, congruence closure) | stable |
| Arrays (read-over-write) | core |
| Bit-vectors | partial |
| Strings | partial |
| Floating-point (ground) | partial |
| Quantifiers (instantiation) | partial |
| Non-linear arithmetic | partial |
| SMT-LIB 2.6 front-end (`set-logic`, `declare/define-fun`, `assert`, `check-sat`, `get-model`, `get-value`, `push`/`pop`, …) | subset |

The **linear-arithmetic core is complete**: the feasibility Simplex terminates on every input
(no `Unknown` from cycling), proven by a randomized termination test. This is the part of the
solver intended for production use today.

## Scope and limitations (vs. Z3)

Z3 (Microsoft Research) is a mature, ~17-year solver. `rz3` deliberately implements the
*subset* needed for deterministic, exact, embeddable reasoning — much as a focused tool covers
the part of a large system that a given workload actually needs. Honestly, relative to Z3:

- **Smaller theory coverage.** Bit-vectors, strings, floating-point, quantifiers and non-linear
  arithmetic are partial; Z3's are complete and battle-tested.
- **No optimization** (`maximize`/`minimize`, à la νZ).
- **Partial proof/unsat-core/interpolation** support.
- **A subset of SMT-LIB 2.6**, not the full standard.
- **Less performance tuning.** Z3 has two decades of engineering; `rz3` favors correctness,
  exactness and determinism over raw speed.

What `rz3` offers that a C++ solver does not: exact (non-floating-point) verdicts, run-to-run
reproducibility, and `wasm32`/no-FFI deployability with zero native dependencies.

## Usage

```toml
[dependencies]
rz3 = "0.1"
```

```rust
use rz3::Rz3Solver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;

let mut s = Rz3Solver::new();
// x > 0 ∧ x < 0  →  Unsat (exact, deterministic)
let x = || Expr::Var("x".into(), Type::Int);
s.assert(&Expr::Gt(Box::new(x()), Box::new(Expr::Int(0))));
s.assert(&Expr::Lt(Box::new(x()), Box::new(Expr::Int(0))));
assert!(matches!(s.check(), SolverResult::Unsat));
```

There is also an SMT-LIB 2.6 front-end binary (`rz3`) for `.smt2` files.

## Project structure

- `src/ast` — logical and arithmetic expressions (exact `Real(numer, scale)`, no `f64`).
- `src/sat` — deterministic CDCL SAT engine.
- `src/theory` — theory solvers (LRA Simplex, EUF, arrays, bit-vectors, FP, strings, …).
- `src/parser` — SMT-LIB 2.6 lexer/parser.

## Determinism & exactness guarantees

- No `rand` and no parallelism in the decision path; all tie-breaks are by index.
- Collections that affect decisions are `BTreeMap`/`BTreeSet` (ordered), never `HashMap`.
- Arithmetic is `num-rational`/`num-bigint`; strict inequalities use a symbolic infinitesimal
  `δ` (Dutertre–de Moura), and Simplex anti-cycling uses a lexicographic `ε`-perturbation —
  both symbolic, so results stay exact.
- An `n=30` harness asserts bit-identical results (SHA-256) across repeated independent solves.

## License

Licensed under either of **MIT** ([LICENSE-MIT](LICENSE-MIT)) or **Apache-2.0**
([LICENSE-APACHE](LICENSE-APACHE)) at your option.

> "Z3" is a generic, widely-shared name (the Zuse Z3 of 1941 was the first programmable
> computer; Z3 is also Microsoft Research's SMT solver). `rz3` is an independent pure-Rust
> implementation and is not affiliated with or derived from Microsoft's Z3.
