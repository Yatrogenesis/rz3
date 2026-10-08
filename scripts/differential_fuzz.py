#!/usr/bin/env python3
"""Differential fuzzer: random QF_{LRA,LIA,UF,BV,mixed} scripts, rz3 vs z3.

Pass criterion: zero sat/unsat disagreements. `unknown`, parse errors on
constructs rz3 declines, and timeouts are counted and reported, never hidden.

usage: fuzz_diff.py <rz3> <z3> <n> <seed> [outdir]
"""
import json
import os
import random
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

RZ3, Z3, N, SEED = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
OUT = sys.argv[5] if len(sys.argv) > 5 else "fuzz_out"
TIMEOUT = 20


class Gen:
    def __init__(self, rng, profile):
        self.r = rng
        self.profile = profile
        self.defs = []  # (name, params, sort, body)

    # --- terms ---
    def int_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return r.choice(["a", "b", "c", str(r.randint(0, 6)), f"(- {r.randint(1, 6)})"])
        k = r.random()
        if k < 0.25:
            return f"(+ {self.int_term(d-1)} {self.int_term(d-1)})"
        if k < 0.45:
            return f"(- {self.int_term(d-1)} {self.int_term(d-1)})"
        if k < 0.55:
            return f"(- {self.int_term(d-1)})"
        if k < 0.65:
            return f"(* {r.randint(-3, 4)} {self.int_term(d-1)})"
        if k < 0.80:
            return f"(ite {self.bool_term(d-1)} {self.int_term(d-1)} {self.int_term(d-1)})"
        if k < 0.90 and self.profile in ("uf", "mixed"):
            return f"(f {self.int_term(d-1)})"
        if k < 0.95:
            return f"(let ((t {self.int_term(d-1)})) (+ t {r.choice(['t','1','a'])}))"
        return r.choice(["a", "b"])

    def real_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return r.choice(["x", "y", "z", f"{r.randint(0, 5)}.{r.randint(0, 9)}", f"(- {r.randint(1, 4)}.0)"])
        k = r.random()
        if k < 0.3:
            return f"(+ {self.real_term(d-1)} {self.real_term(d-1)})"
        if k < 0.55:
            return f"(- {self.real_term(d-1)} {self.real_term(d-1)})"
        if k < 0.65:
            return f"(- {self.real_term(d-1)})"
        if k < 0.75:
            return f"(* {r.randint(-2, 3)}.5 {self.real_term(d-1)})"
        if k < 0.85:
            return f"(/ {self.real_term(d-1)} {r.choice(['2.0','4.0','3.0'])})"
        return f"(ite {self.bool_term(d-1)} {self.real_term(d-1)} {self.real_term(d-1)})"

    def bv_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return r.choice(["p", "q", "s", f"#x{r.randint(0, 255):02x}", f"#b{r.randint(0, 255):08b}", f"(_ bv{r.randint(0,255)} 8)"])
        k = r.random()
        two = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvlshr", "bvashr"]
        if k < 0.65:
            return f"({r.choice(two)} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        if k < 0.75:
            return f"(bvnot {self.bv_term(d-1)})"
        if k < 0.85:
            return f"(concat ((_ extract 3 0) {self.bv_term(d-1)}) ((_ extract 7 4) {self.bv_term(d-1)}))"
        if k < 0.92:
            return f"(ite {self.bool_term(d-1)} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        return f"((_ extract 7 0) {self.bv_term(d-1)})"

    def atom(self, d):
        r = self.r
        kinds = {
            "lia": ["int", "int", "int", "bool"],
            "lra": ["real", "real", "real", "bool"],
            "diff": ["diff", "diff", "diff", "bool"],
            "uf": ["int", "uf", "bool"],
            "bv": ["bv", "bv", "bv", "bool"],
            "mixed": ["int", "real", "bv", "uf", "diff", "bool"],
        }[self.profile]
        k = r.choice(kinds)
        if k == "int":
            op = r.choice(["<", "<=", ">", ">=", "="])
            return f"({op} {self.int_term(d)} {self.int_term(d)})"
        if k == "real":
            op = r.choice(["<", "<=", ">", ">=", "="])
            return f"({op} {self.real_term(d)} {self.real_term(d)})"
        if k == "diff":
            v = r.sample(["a", "b", "c"], 2)
            op = r.choice(["<=", "<", ">=", ">", "="])
            return f"({op} (- {v[0]} {v[1]}) {r.randint(-2, 2)})"
        if k == "bv":
            op = r.choice(["=", "bvult", "bvule", "bvslt", "bvsle", "bvugt", "bvuge", "bvsgt", "bvsge", "distinct"])
            return f"({op} {self.bv_term(d)} {self.bv_term(d)})"
        if k == "uf":
            return r.choice([
                f"(= (f {self.int_term(max(d-1,0))}) (f {self.int_term(max(d-1,0))}))",
                f"(pr {self.int_term(max(d-1,0))})",
                f"(distinct (f a) (f b) (f c))",
                f"(= (f a) {r.randint(0, 3)})",
            ])
        return r.choice(["m", "n", "o", "true", "false"])

    def bool_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.3:
            return self.atom(0)
        k = r.random()
        if k < 0.2:
            return f"(and {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.4:
            return f"(or {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.5:
            return f"(not {self.bool_term(d-1)})"
        if k < 0.6:
            return f"(=> {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.68:
            return f"(xor {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.76:
            return f"(= {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.84:
            return f"(ite {self.bool_term(d-1)} {self.bool_term(d-1)} {self.bool_term(d-1)})"
        if k < 0.9:
            return f"(distinct a b c)" if self.profile in ("lia", "mixed", "diff") else self.atom(d)
        return self.atom(d)

    def script(self):
        r = self.r
        lines = ["(set-logic ALL)"]
        lines += [f"(declare-fun {v} () Int)" for v in "abc"]
        lines += [f"(declare-const {v} Real)" for v in "xyz"]
        lines += [f"(declare-fun {v} () (_ BitVec 8))" for v in "pqs"]
        lines += [f"(declare-fun {v} () Bool)" for v in "mno"]
        lines += ["(declare-fun f (Int) Int)", "(declare-fun pr (Int) Bool)"]
        if r.random() < 0.3:
            lines.append(f"(define-fun k () Int {r.randint(-2, 5)})")
            lines.append("(define-fun dbl ((u Int)) Int (+ u u))")
            if self.profile in ("lia", "mixed"):
                lines.append(f"(assert (> (dbl a) k))")
        boost = int(os.environ.get("FUZZ_BOOST", "0"))
        for _ in range(r.randint(1, 4 + boost)):
            lines.append(f"(assert {self.bool_term(r.randint(1, 3 + boost))})")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"


def run(bin_args, path):
    try:
        p = subprocess.run(bin_args + [path], capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    out = p.stdout.strip()
    toks = [t for t in out.split() if t in ("sat", "unsat", "unknown")]
    if "panicked" in p.stderr or p.returncode < 0:
        return "crash", p.stderr[:200]
    if "(error" in out and not toks:
        return "error", out[:200]
    return (toks[-1] if toks else "none"), out[:200]


def one(i):
    rng = random.Random(SEED * 1_000_003 + i)
    profile = rng.choice(["lia", "lra", "diff", "uf", "bv", "mixed"])
    text = Gen(rng, profile).script()
    path = os.path.join(OUT, f"case_{i}.smt2")
    with open(path, "w") as fh:
        fh.write(text)
    a, ad = run([RZ3], path)
    b, bd = run([Z3, "-smt2", "smt.random_seed=0"], path)
    return i, profile, a, b, path, ad, bd


def main():
    os.makedirs(OUT, exist_ok=True)
    stats = {}
    bad = []
    with ThreadPoolExecutor(max_workers=3) as ex:
        for i, profile, a, b, path, ad, bd in ex.map(one, range(N)):
            key = (profile, a if b in ("sat", "unsat") else f"z3:{b}")
            stats[key] = stats.get(key, 0) + 1
            if a in ("sat", "unsat") and b in ("sat", "unsat") and a != b:
                bad.append({"case": path, "profile": profile, "rz3": a, "z3": b})
            elif a == "crash":
                bad.append({"case": path, "profile": profile, "rz3": "crash", "detail": ad, "z3": b})
            elif a == "none" or (a == "error" and b in ("sat", "unsat")):
                bad.append({"case": path, "profile": profile, "rz3": a, "detail": ad, "z3": b})
            else:
                # keep only interesting files
                if a == b and not os.environ.get("FUZZ_KEEP"):
                    os.remove(path)
    summary = {}
    for (profile, a), n in sorted(stats.items()):
        summary.setdefault(profile, {})[a] = n
    print(json.dumps({"n": N, "seed": SEED, "summary": summary,
                      "disagreements": [x for x in bad if x.get("rz3") in ("sat", "unsat")],
                      "crashes_or_errors": [x for x in bad if x.get("rz3") not in ("sat", "unsat")][:20],
                      "n_disagreements": sum(1 for x in bad if x.get("rz3") in ("sat", "unsat")),
                      "n_crash_or_error": sum(1 for x in bad if x.get("rz3") not in ("sat", "unsat"))},
                     indent=1))


main()
