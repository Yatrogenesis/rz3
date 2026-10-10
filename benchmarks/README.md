# Benchmarks and verification tools

These tools reproduce the evidence quoted in the top-level `README`. They do not measure speed
under a frozen protocol; that comparison is prepared separately.

| Path | What it does |
|---|---|
| `release_gate.py` | Builds the binary of an exact commit in a clean checkout and runs eight checks (formatting and lints, tests, no stubs, generated exercises, the cvc5 regression suite, adversarial scripts, differential fuzz, determinism). A wrong answer in any layer fails the gate. |
| `verified_exercises/gen_exercises.py` | Generates instances (pigeonhole, n-queens, knapsack, job-shop, bit-vector identities, graph colouring, linear feasibility) whose expected answer comes from a solver-free oracle. Deterministic for a given seed. `run_exercises.py` compares solvers with it. |
| `external/cvc5_regress.py` | Runs solvers on the files of cvc5's regression suite that state an expected verdict (selection rule documented in the script). The suite is cloned separately (see the comment at the top of the script). |
| `../scripts/differential_fuzz.py` | Random scripts compared with Z3; any `sat`/`unsat` disagreement is reported. |
| `../tests/adversarial/` | Hand-written scripts, each compared with Z3 by the release gate. |

Example:

```sh
python3 -I benchmarks/release_gate.py --commit HEAD --z3 /path/to/z3 --cvc5 /path/to/cvc5 \
  --exercises set1 hard1 --cvc5-src /path/to/cvc5src --fuzz-n 300
```

Reference solvers used so far: Z3 5.1.0, cvc5 1.4.2, Yices 2.7.0, Bitwuzla 0.9.1.
