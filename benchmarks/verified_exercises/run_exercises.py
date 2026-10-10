#!/usr/bin/env python3
"""Run solvers on the generated exercises and compare with the oracle status in each file.
usage: run_exercises.py <dir> <timeout> <name=binary[;args]> ..."""
import os, re, subprocess, sys, time, collections
d, tmo = sys.argv[1], float(sys.argv[2])
solvers = [a.split("=", 1) for a in sys.argv[3:]]
files = sorted(f for f in os.listdir(d) if f.endswith(".smt2"))
res = collections.defaultdict(collections.Counter); wrong = []; bylog = collections.defaultdict(lambda: collections.defaultdict(collections.Counter))
for f in files:
    p = os.path.join(d, f)
    truth = re.search(r":status (sat|unsat)", open(p).read()).group(1)
    fam = f.split("__")[1]
    for name, cmd in solvers:
        t = time.time()
        try:
            o = subprocess.run(cmd.split(";") + [p], capture_output=True, text=True, timeout=tmo, stdin=subprocess.DEVNULL).stdout.split()
            v = next((x for x in o if x in ("sat", "unsat", "unknown")), "error")
        except subprocess.TimeoutExpired:
            v = "timeout"
        k = "correct" if v == truth else ("WRONG" if v in ("sat", "unsat") else v)
        res[name][k] += 1; bylog[fam][name][k] += 1
        if k == "WRONG": wrong.append((name, f, truth, v))
for name, _ in solvers: print(name, dict(res[name]))
for fam in sorted(bylog): print(f"  {fam:12s}", {n: dict(bylog[fam][n]) for n, _ in solvers})
for w in wrong: print("WRONG", w)
