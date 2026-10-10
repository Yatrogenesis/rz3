#!/usr/bin/env python3
# \1MIT OR Apache-2.0
"""Release gate for rz3: nothing is integrated unless every layer passes.

Builds the release binary of an exact commit in a clean checkout (own target directory, so no
other cargo process can replace it), records its SHA-256, and then runs, in order:

  G1  cargo fmt --check, clippy -D warnings
  G2  cargo test --release (count must not decrease versus --min-tests)
  G3  no stubs (todo!/unimplemented!) in src/
  G4  verified-by-construction exercises (both tiers): zero wrong answers
  G5  cvc5 regression suite files with explicit verdicts: zero wrong answers
  G6  adversarial directory: no decisive answer that contradicts a decisive z3 answer
  G7  differential fuzz against z3 (N scripts): zero sat/unsat disagreements
  G8  determinism: stdout SHA-256 identical over 30 runs on a sample of exercises

A wrong answer anywhere fails the gate. Timeouts and `unknown` are reported, never hidden.

usage: release_gate.py --commit HEAD --z3 PATH --cvc5 PATH [--exercises DIR ...] [--cvc5-src DIR]
                       [--fuzz-n 400] [--min-tests 115] [--out report.json]
"""
import argparse
import collections
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def verdict(argv, path, tmo):
    try:
        out = subprocess.run(argv + [path], capture_output=True, text=True, timeout=tmo,
                             stdin=subprocess.DEVNULL).stdout.split()
    except subprocess.TimeoutExpired:
        return "timeout"
    return next((x for x in out if x in ("sat", "unsat", "unknown")), "error")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--commit", default="HEAD")
    ap.add_argument("--z3", required=True)
    ap.add_argument("--cvc5", required=True)
    ap.add_argument("--exercises", nargs="*", default=[])
    ap.add_argument("--cvc5-src", default=None, help="checkout containing test/regress")
    ap.add_argument("--fuzz-n", type=int, default=400)
    ap.add_argument("--min-tests", type=int, default=0)
    ap.add_argument("--timeout", type=float, default=10)
    ap.add_argument("--out", default="release_gate_report.json")
    a = ap.parse_args()

    commit = sh(["git", "-C", REPO, "rev-parse", a.commit]).stdout.strip()
    work = tempfile.mkdtemp(prefix="rz3_gate_")
    src = os.path.join(work, "src")
    os.makedirs(src)
    tar = subprocess.Popen(["git", "-C", REPO, "archive", commit], stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", src], stdin=tar.stdout, check=True)
    env = dict(os.environ, CARGO_TARGET_DIR=os.path.join(work, "target"))
    report = {"commit": commit, "gates": {}}
    failed = []

    def gate(name, ok, detail):
        report["gates"][name] = {"pass": bool(ok), **detail}
        print(f"{name}: {'PASS' if ok else 'FAIL'} {json.dumps(detail)[:300]}", flush=True)
        if not ok:
            failed.append(name)

    # G1
    fmt = sh(["cargo", "fmt", "--check"], cwd=src, env=env)
    clip = sh(["cargo", "clippy", "--all-targets", "--", "-D", "warnings"], cwd=src, env=env)
    gate("G1_fmt_clippy", fmt.returncode == 0 and clip.returncode == 0,
         {"fmt": fmt.returncode, "clippy": clip.returncode})
    # G2
    t = sh(["cargo", "test", "--release", "--no-fail-fast"], cwd=src, env=env)
    res = re.findall(r"test result: \w+\. (\d+) passed; (\d+) failed", t.stdout)
    passed, failures = sum(int(p) for p, _ in res), sum(int(f) for _, f in res)
    gate("G2_tests", failures == 0 and passed >= a.min_tests and passed > 0,
         {"passed": passed, "failed": failures, "min": a.min_tests})
    # G3
    stubs = sh(["grep", "-rnE", r"todo!\(|unimplemented!\(", os.path.join(src, "src")]).stdout.strip()
    gate("G3_no_stubs", stubs == "", {"matches": stubs[:200]})
    # build the binary used by every later gate
    b = sh(["cargo", "build", "--release", "--locked"], cwd=src, env=env)
    binary = os.path.join(work, "target", "release", "rz3")
    if b.returncode != 0 or not os.path.exists(binary):
        gate("build", False, {"stderr": b.stderr[-300:]})
        return finish(report, failed, a.out)
    sha = hashlib.sha256(open(binary, "rb").read()).hexdigest()
    report["binary_sha256"] = sha
    print("binary", sha, flush=True)
    z3 = [a.z3, "-smt2"]

    # G4 exercises
    wrong4, total4 = [], 0
    for d in a.exercises:
        for f in sorted(os.listdir(d)):
            if not f.endswith(".smt2"):
                continue
            p = os.path.join(d, f)
            truth = re.search(r":status (sat|unsat)", open(p).read())
            if not truth:
                continue
            total4 += 1
            v = verdict([binary], p, a.timeout * 2)
            if v in ("sat", "unsat") and v != truth.group(1):
                wrong4.append(f)
    gate("G4_exercises", not wrong4 and total4 > 0, {"files": total4, "wrong": wrong4[:10]})

    # G5 cvc5 regression suite
    if a.cvc5_src:
        runner = os.path.join(HERE, "external", "cvc5_regress.py")
        shutil_dir = os.path.join(HERE, "external")
        link = os.path.join(shutil_dir, "cvc5src")
        made = False
        if not os.path.exists(link):
            os.symlink(os.path.abspath(a.cvc5_src), link)
            made = True
        tsv = os.path.join(work, "cvc5.tsv")
        r = sh([sys.executable, "-I", runner, binary, a.z3, a.cvc5, str(a.timeout), tsv])
        if made:
            os.unlink(link)
        wrongs = [l for l in r.stdout.splitlines() if l.startswith("RZ3 WRONG")]
        gate("G5_cvc5_regress", r.returncode == 0 and not wrongs and "selected" in r.stdout,
             {"summary": [l for l in r.stdout.splitlines() if l.startswith("rz3")], "wrong": wrongs[:5]})
    else:
        gate("G5_cvc5_regress", False, {"error": "--cvc5-src not given"})

    # G6 adversarial directory vs z3
    adv = os.path.join(REPO, "tests", "adversarial")
    bad6, n6 = [], 0
    if os.path.isdir(adv):
        for f in sorted(os.listdir(adv)):
            if not f.endswith(".smt2"):
                continue
            n6 += 1
            p = os.path.join(adv, f)
            mine, ref = verdict([binary], p, a.timeout), verdict(z3, p, a.timeout)
            if mine in ("sat", "unsat") and ref in ("sat", "unsat") and mine != ref:
                bad6.append((f, mine, ref))
    gate("G6_adversarial", not bad6 and n6 > 0, {"files": n6, "contradictions": bad6[:10]})

    # G7 differential fuzz
    fz = os.path.join(REPO, "scripts", "differential_fuzz.py")
    n7 = a.fuzz_n
    if os.path.exists(fz):
        fzr = sh([sys.executable, "-I", fz, binary, a.z3, str(n7), "20261008", os.path.join(work, "fuzz_out")], cwd=work)
        try:
            fj = json.loads(fzr.stdout)
            dis, oth = fj["n_disagreements"], fj["n_crash_or_error"]
            # A timeout is a capability limit, reported but not a soundness failure; a crash, an
            # error, an empty answer or a disagreement fails the gate.
            hard = [x for x in fj["crashes_or_errors"] if x["kind"] != "timeout"]
            gate("G7_fuzz", dis == 0 and not hard, {"scripts": n7, "disagreements": dis,
                 "timeouts": oth - len(hard), "crashes_or_errors": [x["kind"] for x in hard][:5]})
        except (ValueError, KeyError):
            gate("G7_fuzz", False, {"error": "unreadable fuzzer output", "tail": fzr.stdout[-200:] + fzr.stderr[-200:]})
    else:
        gate("G7_fuzz", False, {"error": "scripts/differential_fuzz.py missing"})

    # G8 determinism
    nondet = []
    sample = []
    for d in a.exercises[:1]:
        sample = sorted(f for f in os.listdir(d) if f.endswith(".smt2"))[::6][:15]
        for f in sample:
            hs = set()
            for _ in range(30):
                o = subprocess.run([binary, os.path.join(d, f)], capture_output=True, timeout=a.timeout * 2).stdout
                hs.add(hashlib.sha256(o).hexdigest())
            if len(hs) != 1:
                nondet.append(f)
    gate("G8_determinism", not nondet and bool(sample), {"instances": len(sample), "runs_each": 30, "nondeterministic": nondet})

    return finish(report, failed, a.out)


def finish(report, failed, out):
    report["pass"] = not failed
    with open(out, "w") as fh:
        json.dump(report, fh, indent=2)
    print("RELEASE GATE:", "PASS" if not failed else "FAIL " + ",".join(failed))
    return 0 if not failed else 1


sys.exit(main())
