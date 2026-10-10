#!/usr/bin/env python3
"""Generates tests/data/fp_z3_table.txt: concrete IEEE 754-2019 results computed by Z3.

Usage: gen_fp_z3_table.py <z3-binary> <output-file>

Every expected value in the table is produced by Z3 (fp.add/sub/mul/div/sqrt/min/max,
comparisons, classification, to_fp from real); this script only enumerates operands
(structural edge values of each format plus a fixed-seed pseudo-random sample) and
renders Z3's answer. Nothing is computed by rz3 or by Python float arithmetic.
"""
import random
import re
import subprocess
import sys
from fractions import Fraction

z3, out_path = sys.argv[1], sys.argv[2]
MODES = ["RNE", "RTZ", "RTP", "RTN"]
FORMATS = [  # name, eb, sb, mode: 'gen' structural+random, 'all' exhaustive
    ("b16", 5, 11, "gen"), ("b32", 8, 24, "gen"), ("b64", 11, 53, "gen"),
    ("f23", 2, 3, "all"), ("f34", 3, 4, "gen"), ("f35", 3, 5, "gen"),
]


def hexw(n, bits):
    return format(n, "0%dx" % ((bits + 3) // 4))


def bitstr(n, bits):
    return format(n, "0%db" % bits)


def fields(eb, sb, sign, e, f):
    return (sign << (eb + sb - 1)) | (e << (sb - 1)) | f


def structural(eb, sb):
    fb = sb - 1
    bias = (1 << (eb - 1)) - 1
    emax = (1 << eb) - 1
    allf = (1 << fb) - 1
    top = 1 << (fb - 1)
    third = int("01" * fb, 2) & allf if fb > 1 else 1
    pats = [
        (0, 0, 0), (1, 0, 0), (0, 0, 1), (1, 0, 1), (0, 0, allf), (0, 1, 0), (0, 1, 1),
        (0, bias, 0), (0, bias, 1), (0, bias - 1, allf), (1, bias, 0), (0, bias + 1, 0),
        (0, bias, top), (0, bias + 1, top), (0, bias - 1, 0), (0, emax - 1, allf),
        (1, emax - 1, allf), (0, emax, 0), (1, emax, 0), (0, emax, top),
        (0, max(bias - 2, 1), third), (0, min(bias + fb, emax - 1), 0),
        (0, min(bias + fb, emax - 1), 1), (0, min(bias + fb + 1, emax - 1), 0),
        (1, 0, allf), (0, emax - 1, 0),
    ]
    seen, res = set(), []
    for s, e, f in pats:
        b = fields(eb, sb, s, e, f)
        if b not in seen:
            seen.add(b)
            res.append(b)
    return res


def is_nan(eb, sb, b):
    e = (b >> (sb - 1)) & ((1 << eb) - 1)
    return e == (1 << eb) - 1 and (b & ((1 << (sb - 1)) - 1)) != 0


def canon_nan(eb, sb):
    return fields(eb, sb, 0, (1 << eb) - 1, 1 << (sb - 2))


def lit(eb, sb, b):
    if is_nan(eb, sb, b):
        return "(_ NaN %d %d)" % (eb, sb)
    return "((_ to_fp %d %d) #b%s)" % (eb, sb, bitstr(b, eb + sb))


queries = []  # (smt-expression, kind, fmt-context)


def run(exprs):
    text = "\n".join("(simplify %s)" % e for e in exprs) + "\n"
    r = subprocess.run([z3, "-in"], input=text, capture_output=True, text=True, check=True)
    outs, depth, cur = [], 0, ""
    for tok in re.findall(r"\(|\)|[^\s()]+", r.stdout):
        if tok == "(":
            depth += 1
            cur += "( "
        elif tok == ")":
            depth -= 1
            cur += ") "
            if depth == 0:
                outs.append(cur.strip())
                cur = ""
        else:
            cur += tok + " "
            if depth == 0:
                outs.append(cur.strip())
                cur = ""
    if len(outs) != len(exprs):
        raise SystemExit("z3 output mismatch %d vs %d\n%s" % (len(outs), len(exprs), r.stdout[:2000]))
    return outs


def parse_fp(eb, sb, s):
    s = s.replace("( ", "(").replace(" )", ")")
    if "NaN" in s:
        return "N"
    m = re.match(r"\(fp (#[bx][0-9a-f]+) (#[bx][0-9a-f]+) (#[bx][0-9a-f]+)\)", s)
    if m:
        def tok(t):
            return bin(int(t[2:], 16))[2:].zfill(4 * (len(t) - 2)) if t[1] == "x" else t[2:]
        return hexw(int(tok(m.group(1)) + tok(m.group(2)) + tok(m.group(3)), 2), eb + sb)
    m = re.match(r"\(_ ([+-])(zero|oo) ", s)
    if m:
        sign = 1 if m.group(1) == "-" else 0
        e, f = (0, 0) if m.group(2) == "zero" else ((1 << eb) - 1, 0)
        return hexw(fields(eb, sb, sign, e, f), eb + sb)
    raise SystemExit("unparsed fp: " + s)


def rnd_patterns(eb, sb, rng, n):
    pairs = []
    emax = (1 << eb) - 1
    fb = sb - 1
    for i in range(n):
        s1, s2 = rng.getrandbits(1), rng.getrandbits(1)
        e1 = rng.randrange(0, emax)
        if i % 2:
            e2 = min(max(e1 + rng.randrange(-3, 4), 0), emax - 1)
        else:
            e2 = rng.randrange(0, emax)
        f1, f2 = rng.getrandbits(fb), rng.getrandbits(fb)
        if rng.random() < 0.3:
            f1 &= ~((1 << rng.randrange(0, fb)) - 1)  # trailing zeros => exact/tie cases
        pairs.append((fields(eb, sb, s1, e1, f1), fields(eb, sb, s2, e2, f2)))
    return pairs


lines = []
for name, eb, sb, mode in FORMATS:
    rng = random.Random(0x1EEE754 + eb * 100 + sb)
    W = eb + sb
    if mode == "all":
        vals = [b for b in range(1 << W) if not is_nan(eb, sb, b)] + [canon_nan(eb, sb)]
    else:
        vals = structural(eb, sb)
    pairs = [(a, b) for a in vals for b in vals]
    if mode == "gen" and sb > 5:
        pairs += rnd_patterns(eb, sb, rng, 150)
    # binary operations: one line per (op,a,b) with the four modes
    for op in ["add", "sub", "mul", "div"]:
        ex = []
        for a, b in pairs:
            for m in MODES:
                ex.append("(fp.%s %s %s %s)" % (op, m, lit(eb, sb, a), lit(eb, sb, b)))
        res = run(ex)
        for i, (a, b) in enumerate(pairs):
            r = res[4 * i:4 * i + 4]
            lines.append("%s %s %s %s %s" % (op, name, hexw(a, W), hexw(b, W),
                                             " ".join(parse_fp(eb, sb, x) for x in r)))
    # sqrt
    svals = vals + [x for x, _ in rnd_patterns(eb, sb, rng, 120)] if mode == "gen" and sb > 5 else vals
    ex = ["(fp.sqrt %s %s)" % (m, lit(eb, sb, a)) for a in svals for m in MODES]
    res = run(ex)
    for i, a in enumerate(svals):
        lines.append("sqrt %s %s - %s" % (name, hexw(a, W),
                                         " ".join(parse_fp(eb, sb, x) for x in res[4 * i:4 * i + 4])))
    # min / max (fp.min of +0/-0 is unspecified in SMT-LIB: the line carries '?')
    for op in ["min", "max"]:
        mm_pairs = [(a, b) for a in vals for b in vals]
        ex = ["(fp.%s %s %s)" % (op, lit(eb, sb, a), lit(eb, sb, b)) for a, b in mm_pairs]
        res = run(ex)
        for (a, b), x in zip(mm_pairs, res):
            ok = x.replace("( ", "(").replace(" )", ")")
            r = "?" if ("fp.m" in ok or "unspecified" in ok) else parse_fp(eb, sb, x)
            lines.append("%s %s %s %s %s" % (op, name, hexw(a, W), hexw(b, W), r))
    # comparisons and structural equality over the structural set
    cmp_pairs = [(a, b) for a in vals for b in vals]
    ops = ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq", "="]
    ex = ["(%s %s %s)" % (o, lit(eb, sb, a), lit(eb, sb, b)) for a, b in cmp_pairs for o in ops]
    res = run(ex)
    for i, (a, b) in enumerate(cmp_pairs):
        bits = "".join("1" if x == "true" else "0" for x in res[6 * i:6 * i + 6])
        lines.append("cmp %s %s %s %s" % (name, hexw(a, W), hexw(b, W), bits))
    # classification
    preds = ["fp.isNormal", "fp.isSubnormal", "fp.isNaN", "fp.isInfinite", "fp.isZero",
             "fp.isPositive", "fp.isNegative"]
    ex = ["(%s %s)" % (p, lit(eb, sb, a)) for a in vals for p in preds]
    res = run(ex)
    for i, a in enumerate(vals):
        bits = "".join("1" if x == "true" else "0" for x in res[7 * i:7 * i + 7])
        lines.append("cls %s %s %s" % (name, hexw(a, W), bits))
    # to_fp from real
    pos = [b for b in vals if not is_nan(eb, sb, b) and not (b >> (W - 1)) and
           ((b >> (sb - 1)) & ((1 << eb) - 1)) != (1 << eb) - 1 and b != 0]
    pos.sort()

    def val(b):
        e = (b >> (sb - 1)) & ((1 << eb) - 1)
        f = b & ((1 << (sb - 1)) - 1)
        bias = (1 << (eb - 1)) - 1
        if e == 0:
            return Fraction(f, 1 << (sb - 1)) * Fraction(2) ** (1 - bias)
        return (1 + Fraction(f, 1 << (sb - 1))) * Fraction(2) ** (e - bias)

    bias = (1 << (eb - 1)) - 1
    ulp_top = Fraction(2) ** ((((1 << eb) - 2) - bias) - (sb - 1))
    maxv = val(fields(eb, sb, 0, (1 << eb) - 2, (1 << (sb - 1)) - 1))
    minsub = Fraction(2) ** (1 - bias - (sb - 1))
    rats = set()
    eps = Fraction(1, 2 ** (sb + 12))
    for b in pos:
        v = val(b)
        nxt = val(b + 1) if b != fields(eb, sb, 0, (1 << eb) - 2, (1 << (sb - 1)) - 1) else maxv + ulp_top
        mid = (v + nxt) / 2
        for q in (v, mid, mid * (1 - eps), mid * (1 + eps), v * (1 + eps), v * (1 - eps)):
            rats.add(q)
    for k in (Fraction(1, 2), Fraction(1, 4), Fraction(3, 2), Fraction(5, 2), Fraction(3, 4), Fraction(1, 3),
              Fraction(3, 1), Fraction(1, 10), Fraction(2, 3), Fraction(7, 2)):
        rats.add(minsub * k)
        rats.add(minsub * k * (1 + eps))
        rats.add(minsub * k * (1 - eps))
    for q in (Fraction(1, 3), Fraction(2, 3), Fraction(1, 10), Fraction(7), Fraction(100000), Fraction(65520),
              Fraction(65519), Fraction(16777217), Fraction(5, 2), Fraction(3, 2), Fraction(1), Fraction(2),
              maxv * 2, maxv + ulp_top / 2, maxv + ulp_top / 2 - minsub / 8):
        rats.add(q)
    rats.add(Fraction(0))
    allr = sorted(rats) + sorted(-q for q in rats if q != 0)
    ex = []
    for q in allr:
        num = "(- %d.0)" % -q.numerator if q < 0 else "%d.0" % q.numerator
        for m in MODES:
            ex.append("((_ to_fp %d %d) %s (/ %s %d.0))" % (eb, sb, m, num, q.denominator))
    res = run(ex)
    for i, q in enumerate(allr):
        lines.append("real %s %d %d %s" % (name, q.numerator, q.denominator,
                                         " ".join(parse_fp(eb, sb, x) for x in res[4 * i:4 * i + 4])))

with open(out_path, "w") as fh:
    fh.write("# Z3-generated IEEE 754-2019 oracle table (see gen_fp_z3_table.py). Do not edit.\n")
    fh.write("# fmt: b16(5,11) b32(8,24) b64(11,53) f23(2,3) f34(3,4) f35(3,5); results RNE RTZ RTP RTN; N=NaN\n")
    fh.write("\n".join(lines) + "\n")
print(len(lines), "lines")
