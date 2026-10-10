# Changelog

All notable changes to `rz3` are documented here. Format based on
[Keep a Changelog](https://keepachangelog.com/); this project follows semantic versioning.

## [0.2.0] — 2026-10-10

Soundness release. A 120-case differential pilot against Z3 5.1.0 showed that `rz3` 0.1.4 answered
`sat` on 56 of 60 unsatisfiable controls and could answer `unsat` on satisfiable inputs. The root
causes were in the SMT-LIB front end, the SAT core and the conflict explanations, not in the
arithmetic algorithms. Later differential, adversarial and mutation testing found further defects,
all listed below.

**Behaviour changes (reason for the minor version bump):**
- Input the solver cannot interpret now produces an error or `unknown`, never a verdict. The
  front end is strict: an unsupported construct stops the run with `(error "...")` and exit
  status 1 instead of being skipped.
- `Command` has new variants (`Skipped`, `DeclareSort`); `Parser::strict` and `Parser::error` are
  new. `src/theory/lra.rs` (`LraSolver`) is deprecated; it is not used by the solver and will be
  removed in a later release.
- A missing input file now exits with status 1. `get-value` of an application of a declared
  function returns its value (it returned an empty list).

### Added
- Incremental linearisation for non-linear real/integer arithmetic (sign, tangent, McCormick and
  monotonicity lemmas); `sat` only when the exact evaluator confirms the model.
- Bit-vectors of any width (up to the bit-blaster limit of 4,096 bits) with arbitrary-precision
  constants; `bvite`, `bvredor`, `bvredand`, `bvnego`, the overflow predicates (`bvuaddo`,
  `bvsaddo`, `bvusubo`, `bvssubo`, `bvumulo`, `bvsmulo`, `bvsdivo`), n-ary `concat`.
- Ring normalisation of bit-vector terms over Z/2^w (`src/bvring.rs`), which decides
  multiplication identities such as `x*(y+z) = x*y + x*z` before bit-blasting.
- Floating point: `Float16/32/64`, the special constants, IEEE comparisons, `fp.min`/`fp.max`,
  `to_fp` from a real literal or a bit pattern; terms that cannot be evaluated (free floating-point
  variables) give `unknown`.
- Scoped `push`/`pop` (declarations, definitions and `:named` terms), `define-const`,
  `(! t :named n)`, `let` with sharing of large bound values, arrays, uninterpreted sorts,
  `div`/`mod`/`abs`/`to_real`/`to_int`/`is_int`.
- Models and `get-value` echoes are printed in standard SMT-LIB syntax (`(- 1)`, `1.0`,
  `(/ 1.0 2.0)`).
- `rz3::driver::check_script`, `rz3::eval` (exact evaluation used to certify every `sat`).
- Tests and tools: 292 tests; 211 generated exercises with solver-free oracles
  (`benchmarks/verified_exercises`); runner for cvc5's regression suite
  (`benchmarks/external`); `benchmarks/release_gate.py`; `scripts/differential_fuzz.py`;
  66 adversarial scripts (`tests/adversarial`); a Z3-generated table of about 31,000
  floating-point operations; 5,049 evaluator cases checked against Z3; end-to-end tests of the
  command-line binary.

### Fixed
- **Front end:** unknown operators (`-`, `distinct`, `=>`, `xor`, all `bv*`, ...) were silently
  turned into uninterpreted applications; `#x..` literals were lexed as integers; numerals over 64
  bits and unknown commands ended the script silently (answering `sat` for the prefix);
  `define-fun` bodies were discarded; chainable `= <= < >= >` kept only two arguments; nested `let`
  was expanded as a tree (exponential memory: 25 of 400 development instances aborted).
- **SAT core:** clauses added on a stale assignment, units lost on backtrack, unassigned variables
  not returned to the decision heap, learnt clauses sorted (breaking the watch invariant).
- **Conflict explanations:** EUF and LRA reported partial cores, so learnt clauses excluded
  satisfiable assignments (spurious `unsat`); cores are now minimal-by-deletion (EUF).
- **Arrays:** the reducer compared index types with `get_type()`, which is `Unknown` for an
  application of an uninterpreted function, and dropped the read-over-write axioms: `f(i) = i`
  together with `select(store(A, f(i), 7), i) /= 7` was reported `sat` (found by an independent
  differential run; Z3, cvc5 and Yices answer `unsat`).
- **Floating point:** an exactly-zero result of `fp.add/sub/mul/div` was always `+0`; IEEE 754-2019
  section 6.3 and Z3 require the signs described there, and SMT-LIB equality distinguishes `+0` from
  `-0`.
- **Division by zero:** `mod x 0` was rewritten to `x`, refuting satisfiable problems; `div`, `mod`
  and `/` by zero are now total functions of the dividend, with consistency lemmas between terms.
- **Congruence closure used with arrays and quantifiers:** a node's identifier was taken before its
  arguments were registered, so `f(c)` with a new argument `c` shared the identifier of `c`
  (no wrong verdict was observed from this path).
- **Tactics and arithmetic:** `SolveEqs` lost equations; constant folding overflowed `i64`;
  `ite` over arithmetic; unary minus; `Int` variables enforced by bound normalisation and
  branch-and-bound; abstracted terms never support a `sat` verdict.
- **Command line:** `get-value` echoed some operators with Rust debug text; a missing input file
  exited with status 0.
- **Bit-vectors:** unsupported operators produced an empty vector (equality then held trivially).

### Verification (commit `b7ba3bd`; `benchmarks/release_gate.py` also ran on `8dc7cb0`)
- 292 tests; `clippy -D warnings` and `fmt --check` clean.
- 211 exercises with solver-free oracles: no wrong answer. cvc5 regression suite, 172 selected
  files with an explicit expected verdict: 157 correct, none wrong. 66 adversarial scripts: no
  contradiction with Z3. Differential fuzz against Z3: no disagreement (400 scripts on the release
  candidate; about 35,000 on earlier snapshots).
- Independent conformance runs against Z3, cvc5 and Yices (Codex: 392 and 208 cases) found one
  wrong answer family (arrays, above), fixed.
- Determinism: 40 satisfiable instances with printed models, 30 independent processes each, byte
  identical; 15 instances x 30 in the release gate.
- Mutation testing (`cargo-mutants`): 63.8% of viable mutants detected over the whole crate before
  the last round of tests; 95.2% (1,314 mutants) in the modules reinforced afterwards. Surviving
  mutants are not all classified.

### Known limits
- No claim is made about speed; preliminary measurements under load showed fewer instances solved
  than Z3 and cvc5.
- Non-linear arithmetic answers `unknown` on a substantial fraction of inputs; quantifier
  instantiation is weak; strings are not supported; floating point is limited to ground terms.
- `unsat` has no independent proof checker.

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
