# rz3 — a deterministic, exact-rational SMT solver in pure Rust

`rz3` is an SMT (Satisfiability Modulo Theories) solver written in Rust with no C/C++
dependencies. A CDCL SAT core drives a set of theory solvers (DPLL(T)). It reads a subset of
SMT-LIB 2.6 and can also be used as a library.

Design goals:

- **Exact arithmetic.** Linear and non-linear arithmetic are computed over arbitrary-precision
  rationals (`num-rational` / `num-bigint`); there is no floating point in the arithmetic core.
- **Deterministic output.** The solver uses no randomness. With no time limit set, the same
  input gives the same output (see *Determinism* below for what has and has not been checked).
- **No native dependencies.** Pure Rust.

`rz3` is a research prototype. It is **not** a replacement for Z3 or cvc5: it supports a subset
of the theories and of the SMT-LIB language, and its answers are `unknown` more often (see
*Scope and limitations*). It makes no claim about speed.

## Answer policy

- `sat` — the model is re-checked by an independent exact evaluator against the original
  assertions. If the evaluator cannot confirm it (for example, a term it cannot interpret), the
  answer is `unknown`, never `sat`.
- `unsat` — derived by the theory reasoning. There is **no independent proof checker**: `unsat`
  is not certified. It is cross-checked against other solvers in the tests described below.
- `unknown` — a sound non-answer. It is returned when a construct is not decided (incomplete
  theory), a resource limit is reached, or a `sat` model cannot be certified.
- Input the front end does not understand produces an explicit error; it is never skipped.

## Scope and limitations

| Area | Status |
|---|---|
| Booleans, CDCL SAT core | Supported. |
| Linear real and integer arithmetic (LRA, LIA), difference logic (IDL, RDL) | Supported: exact simplex with strict bounds, branch-and-bound for integers. A dedicated difference-logic module exists but is off by default. |
| Uninterpreted functions and sorts (EUF) | Supported: congruence closure; functions over arithmetic or bit-vector arguments are reduced by Ackermann's method. |
| Arrays | Supported by reduction (`select`, `store`, constant arrays, extensionality). A satisfiable verdict is withheld when the index sort is a bit-vector narrower than 20 bits. |
| Bit-vectors | All standard operators and the overflow predicates, of any width up to the 4,096-bit limit of the bit-blaster, by bit-blasting. Multiplication and division of wide vectors can be slow. A ring normaliser over Z/2^w resolves multiplication identities before bit-blasting. |
| Non-linear arithmetic (NRA, NIA) | Incremental linearisation (sign, tangent, McCormick and monotonicity lemmas). Sound but incomplete: it answers `unknown` on a substantial fraction of inputs, and does not isolate irrational algebraic numbers. |
| Quantifiers | Skolemisation and instantiation over ground terms. Sound but weak: a universal quantifier can lead to `unsat`, but `sat` is not reported while one remains. Pattern-based E-matching is minimal. |
| Floating point | Ground terms only: IEEE 754 operations are evaluated exactly for `fp.add/sub/mul/div/sqrt/min/max`, comparisons, classification, and `to_fp` from a real literal or a bit pattern. Problems with free floating-point variables answer `unknown`. |
| Strings, regular expressions | Not supported (explicit error). |
| Optimisation, proofs, unsat cores, interpolation | Not supported. |
| `div`, `mod`, `/` by zero | Treated as total functions of the dividend, as the SMT-LIB standard specifies. |

SMT-LIB front end: `set-logic`, `set-option`, `set-info`, `declare-const/fun/sort`,
`define-const/fun/sort`, `assert`, `check-sat`, `get-model`, `get-value`, `push`/`pop` (with
scoped declarations), `exit`, `(! t :named n)`, `let`, and the operators of Core, Ints, Reals,
Reals_Ints, ArraysEx and FixedSizeBitVectors theories, plus a floating-point subset. Other
commands and operators are reported as errors.

## Evidence

Everything below can be reproduced with the scripts of this repository (`benchmarks/`,
`scripts/`, `tests/`) and public external suites, on the commit named in the `CHANGELOG`. None of
it is a proof of correctness.

- `cargo test --release`: 292 tests; `cargo clippy --all-targets -- -D warnings` and
  `cargo fmt --check` are clean.
- `benchmarks/release_gate.py` builds the binary from a clean checkout and runs eight checks:
  formatting and lints, tests, no stubs, 211 generated exercises whose expected answer comes
  from solver-free oracles (exhaustive search, dynamic programming, exact Fourier–Motzkin,
  theorems) with no wrong answer, the files of cvc5's regression suite that state an expected
  verdict (157 of 172 selected files answered correctly, none wrongly), 66 hand-written
  adversarial scripts compared with Z3, a differential fuzz run against Z3 (no disagreement),
  and a determinism check.
- Independent differential runs against Z3, cvc5 and Yices found wrong answers that the
  repository's own fuzzer had not covered (for example arrays indexed by function applications,
  the sign of zero in floating point, and `mod x 0`). All are fixed in 0.2.0; see the `CHANGELOG`.
- Mutation testing with `cargo-mutants`: on the commit before the last round of tests, 63.8% of
  the viable mutants of the whole crate were detected (89.3% in the eight core modules); after
  adding tests, 95.2% of the 1,314 viable mutants of the reinforced modules. Surviving mutants
  are not all classified: many are equivalent or only affect speed. This is not an error rate.
- Preliminary, under load and on an earlier snapshot: on 400 SMT-LIB 2024 instances with a 10 s
  timeout `rz3` solved fewer instances than Z3 and cvc5. A comparison under a pre-registered
  protocol is in preparation; until it is published, assume nothing about speed relative to
  other solvers.

### Determinism

No `rand`; the wall clock is used only by the optional time limit and for statistics. With no
time limit, 40 satisfiable instances (printed models included) gave byte-identical output over
30 independent processes each, and the release gate repeats 15 instances 30 times. Some modules
use hashed collections (`HashMap`) for lookups; the tests above did not find an
ordering-dependent result, but its absence is checked by testing, not proven.

### Portability

The library compiles for `wasm32-unknown-unknown` (`cargo check --target
wasm32-unknown-unknown`). Running on that target has not been tested, and `std::time::Instant`,
used for statistics, panics there.

## Usage

```toml
[dependencies]
rz3 = "0.2"
```

```rust
use rz3::ast::{Expr, Type};
use rz3::{Rz3Solver, SolverResult};

let mut s = Rz3Solver::new();
// x > 0 and x < 0 is unsatisfiable over the integers
let x = || Expr::Var("x".into(), Type::Int);
s.assert(&Expr::Gt(Box::new(x()), Box::new(Expr::Int(0))));
s.assert(&Expr::Lt(Box::new(x()), Box::new(Expr::Int(0))));
assert!(matches!(s.check(), SolverResult::Unsat));
```

Command line (SMT-LIB 2.6 input file):

```sh
cargo run --release --bin rz3 -- problem.smt2
```

Environment variables: `RZ3_DEADLINE_MS` (time limit in milliseconds; a run that hits it
answers `unknown`), `RZ3_STATS` (statistics on stderr).

## Project structure

- `src/ast`, `src/parser.rs`, `src/driver.rs` — expressions, SMT-LIB parser, script driver.
- `src/sat` — CDCL SAT engine with theory hooks.
- `src/theory` — `simplex`, `linarith`, `cc`, `euf`, `array_reduce`, `bv`, `fp`, `quantifier`,
  `skolem`, `diff` and the legacy `lra` / `nla` modules.
- `src/eval.rs` — exact evaluator used to certify `sat`.
- `src/bvring.rs` — ring normalisation of bit-vector terms.
- `tests/`, `benchmarks/`, `scripts/` — tests, generators of exercises with known answers,
  runners for external suites, release gate, differential fuzzer.

`src/theory/lra.rs` is a legacy solver that the main pipeline does not use; it is deprecated and
will be removed from this crate in a later release.

## Reporting a wrong answer

If `rz3` answers `sat` or `unsat` and another solver disagrees, please open an issue with the
input file, the `rz3` version and the other solver's version.

## Citation

See `CITATION.cff`. Version 0.2.0: DOI `10.5281/zenodo.23287042`. The concept DOI
`10.5281/zenodo.20686622` always resolves to the latest archived version; cite the version DOI of
the release you used when reproducing results.

## License

Licensed under either of **MIT** ([LICENSE-MIT](LICENSE-MIT)) or **Apache-2.0**
([LICENSE-APACHE](LICENSE-APACHE)) at your option.

> "Z3" is a generic, widely-shared name (the Zuse Z3 of 1941 was the first programmable
> computer; Z3 is also Microsoft Research's SMT solver). `rz3` is an independent
> implementation and is not affiliated with or derived from Microsoft's Z3.
