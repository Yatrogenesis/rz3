#!/usr/bin/env python3
"""Checks every line of eval_cases_*.txt against Z3.

usage: verify_eval_cases_z3.py /path/to/z3 file...
Each case `vars ; expr ; expected` is rendered as (simplify (let (vars) expr)) and the
value Z3 returns is compared with `expected`. Lines expecting `unknown` are skipped
(the evaluator declines them; Z3 treats e.g. division by zero as uninterpreted).
"""
import subprocess, sys
from fractions import Fraction

def sexp(tokens):
    t = tokens.pop(0)
    if t == "(":
        l = []
        while tokens[0] != ")":
            l.append(sexp(tokens))
        tokens.pop(0)
        return l
    return t

def tok(s):
    return s.replace("(", " ( ").replace(")", " ) ").split()

def norm(e):
    if isinstance(e, list):
        if e[0] == "-" and len(e) == 2: return norm(e[1]) * -1 if not isinstance(norm(e[1]), tuple) else None
        if e[0] == "/": return norm(e[1]) / norm(e[2])
        raise ValueError(e)
    if e in ("true", "false"): return e == "true"
    if e.startswith("#x"): return ("bv", 4 * (len(e) - 2), int(e[2:], 16))
    if e.startswith("#b"): return ("bv", len(e) - 2, int(e[2:], 2))
    return Fraction(e)

def parse_expected(x):
    x = x.strip()
    if x in ("true", "false"): return x == "true"
    if x.startswith("#b"): return ("bv", len(x) - 2, int(x[2:], 2))
    return Fraction(x)

def zval(sort, v):
    v = v.strip()
    if sort in ("Int", "Real"):
        f = Fraction(v)
        s = "(/ %d.0 %d.0)" % (abs(f.numerator), f.denominator) if sort == "Real" else str(abs(f.numerator))
        if sort == "Real" and f.denominator == 1: s = "%d.0" % abs(f.numerator)
        return "(- %s)" % s if f < 0 else s
    return v

def main():
    z3, files = sys.argv[1], sys.argv[2:]
    bad = checked = 0
    for fn in files:
        cases = []
        for ln in open(fn):
            if not ln.strip() or ln.startswith("#"): continue
            vars_, expr, exp = [p.strip() for p in ln.rstrip("\n").split(" ; ")]
            if exp == "unknown": continue
            binds = ""
            if vars_:
                for d in vars_.split(","):
                    name, rest = d.split(":"); sort, v = rest.split("=")
                    binds += "(%s %s)" % (name, zval(sort, v))
            term = "(let (%s) %s)" % (binds, expr) if binds else expr
            cases.append((term, exp, ln.strip()))
        for i in range(0, len(cases), 500):
            chunk = cases[i:i + 500]
            script = "".join('(echo "@%d")(simplify %s)\n' % (j, t) for j, (t, _, _) in enumerate(chunk))
            res = subprocess.run([z3, "-smt2", "-in"], input=script, capture_output=True, text=True).stdout
            parts = res.split('@')[1:]
            assert len(parts) == len(chunk), (len(parts), len(chunk), res[:300])
            for j, (t, exp, line) in enumerate(chunk):
                body = parts[j].split("\n", 1)[1] if "\n" in parts[j] else ""
                try:
                    got = norm(sexp(tok(body)))
                except Exception as e:
                    got = "unparsed:" + body.strip()
                checked += 1
                if got != parse_expected(exp):
                    bad += 1
                    print("MISMATCH", line, "| z3:", body.strip())
    print("checked", checked, "mismatches", bad)
    sys.exit(1 if bad else 0)

main()
