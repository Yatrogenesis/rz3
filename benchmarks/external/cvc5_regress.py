#!/usr/bin/env python3
"""Run solvers on cvc5's regression suite files whose expected verdict is written in the file.

Selection (fixed before looking at any result): the file has exactly one `(check-sat)`, no
push/pop/check-sat-assuming/get-*, a `; EXPECT: sat|unsat` header, a `(set-logic L)` with L in
SCOPE, and no `; COMMAND-LINE` / `; REQUIRES` lines (those change the semantics or need features).
usage: cvc5_regress.py <rz3> <z3> <cvc5> <timeout> [out.tsv]
"""
import os, re, subprocess, sys, hashlib, concurrent.futures as cf
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cvc5src/test/regress")  # git clone --depth 1 --filter=blob:none --sparse https://github.com/cvc5/cvc5 cvc5src && git -C cvc5src sparse-checkout set test/regress/cli
SCOPE = {"QF_LRA","QF_LIA","QF_IDL","QF_RDL","QF_UF","QF_UFLRA","QF_UFLIA","QF_UFIDL","QF_BV","QF_AX","QF_ALIA","QF_AUFLIA","QF_UFBV","QF_ABV","QF_AUFBV","QF_NRA","QF_NIA","LRA","LIA","UF","UFLIA","UFLRA","AUFLIA"}
rz3, z3, cvc5, tmo = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4])
out = sys.argv[5] if len(sys.argv) > 5 else "cvc5_regress_results.tsv"
files = []
for d, _, fs in os.walk(ROOT):
    for f in sorted(fs):
        if not f.endswith(".smt2"): continue
        p = os.path.join(d, f)
        try: t = open(p, errors="replace").read()
        except OSError: continue
        m = re.search(r"^;\s*EXPECT:\s*(sat|unsat)\s*$", t, re.M)
        l = re.search(r"\(set-logic\s+(\S+?)\s*\)", t)
        if not m or not l or l.group(1) not in SCOPE: continue
        if len(re.findall(r"\(check-sat\)", t)) != 1: continue
        if re.search(r"\((push|pop|check-sat-assuming|get-|set-option :incremental)|^;\s*(COMMAND-LINE|REQUIRES|SCRUBBER|EXIT)", t, re.M): continue
        files.append((p, m.group(1), l.group(1)))
files.sort()
def run(argv, p):
    try:
        r = subprocess.run(argv + [p], capture_output=True, text=True, timeout=tmo, stdin=subprocess.DEVNULL)
        w = [x for x in r.stdout.split() if x in ("sat", "unsat", "unknown")]
        return w[0] if w else ("error" if r.returncode else "none")
    except subprocess.TimeoutExpired:
        return "timeout"
def job(item):
    p, exp, logic = item
    return (os.path.relpath(p, ROOT), logic, exp, run([rz3], p), run([z3, "-smt2"], p), run([cvc5, "--lang=smt2"], p))
with cf.ThreadPoolExecutor(2) as ex:
    rows = list(ex.map(job, files))
with open(out, "w") as fh:
    fh.write("file\tlogic\texpected\trz3\tz3\tcvc5\n")
    for r in rows: fh.write("\t".join(r) + "\n")
print("selected", len(rows), "sha256(list)", hashlib.sha256("\n".join(r[0] for r in rows).encode()).hexdigest()[:16])
for name, idx in (("rz3", 3), ("z3", 4), ("cvc5", 5)):
    c = {}
    for r in rows:
        v = r[idx]; k = "correct" if v == r[2] else ("WRONG" if v in ("sat", "unsat") else v)
        c[k] = c.get(k, 0) + 1
    print(name, dict(sorted(c.items())))
for r in rows:
    if r[3] in ("sat", "unsat") and r[3] != r[2]: print("RZ3 WRONG", r)
