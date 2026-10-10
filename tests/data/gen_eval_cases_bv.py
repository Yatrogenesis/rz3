#!/usr/bin/env python3
"""Generates eval_cases_bv.txt: bit-vector evaluator cases at widths 1, 8, 64 and 100.

The expected values come from the SMT-LIB 2.6 *definitional expansions* of the
operators (e.g. bvsdiv/bvsrem/bvsmod via bvudiv/bvurem/bvneg), written here
independently of the Rust evaluator. verify_eval_cases_z3.py then checks every
line against Z3, so the file is contrasted with two oracles.
"""
import sys

def lit(v, w):
    if w % 4 == 0:
        return "#x%0*x" % (w // 4, v)
    return "#b" + format(v, "0%db" % w)

def out(v, w):
    return "#b" + format(v, "0%db" % w)

def udiv(x, y, w):
    return (1 << w) - 1 if y == 0 else x // y

def urem(x, y, w):
    return x if y == 0 else x % y

def neg(x, w):
    return (-x) % (1 << w)

def msb(x, w):
    return (x >> (w - 1)) & 1

def sdiv(s, t, w):
    ms, mt = msb(s, w), msb(t, w)
    if (ms, mt) == (0, 0): return udiv(s, t, w)
    if (ms, mt) == (1, 0): return neg(udiv(neg(s, w), t, w), w)
    if (ms, mt) == (0, 1): return neg(udiv(s, neg(t, w), w), w)
    return udiv(neg(s, w), neg(t, w), w)

def srem(s, t, w):
    ms, mt = msb(s, w), msb(t, w)
    if (ms, mt) == (0, 0): return urem(s, t, w)
    if (ms, mt) == (1, 0): return neg(urem(neg(s, w), t, w), w)
    if (ms, mt) == (0, 1): return urem(s, neg(t, w), w)
    return neg(urem(neg(s, w), neg(t, w), w), w)

def smod(s, t, w):
    ms, mt = msb(s, w), msb(t, w)
    abs_s = neg(s, w) if ms else s
    abs_t = neg(t, w) if mt else t
    u = urem(abs_s, abs_t, w)
    if u == 0: return u
    if (ms, mt) == (0, 0): return u
    if (ms, mt) == (1, 0): return (neg(u, w) + t) % (1 << w)
    if (ms, mt) == (0, 1): return (u + t) % (1 << w)
    return neg(u, w)

def sgn(x, w):
    return x - (1 << w) if msb(x, w) else x

def values(w):
    m = (1 << w) - 1
    vs = [0, 1, m, 1 << (w - 1)]
    if w > 1:
        vs += [(1 << (w - 1)) - 1, 2 if w > 2 else 2 % (1 << w)]
    pat = int(("10100101" * (w // 8 + 1))[:w], 2)
    if w >= 8:
        vs += [pat, neg(7, w)]
    seen, res = set(), []
    for v in vs:
        v &= m
        if v not in seen:
            seen.add(v); res.append(v)
    return res

lines = []
def case(expr, expected):
    lines.append(" ; %s ; %s" % (expr, expected))

def b(x):
    return "true" if x else "false"

for w in (1, 8, 64, 100):
    m = (1 << w) - 1
    V = values(w)
    for x in V:
        X = lit(x, w)
        case("(bvneg %s)" % X, out(neg(x, w), w))
        case("(bvnot %s)" % X, out(m ^ x, w))
        for n in (1, 4, 7):
            case("((_ zero_extend %d) %s)" % (n, X), out(x, w + n))
            case("((_ sign_extend %d) %s)" % (n, X), out(sgn(x, w) % (1 << (w + n)), w + n))
        for n in (0, 1, 3, w - 1, w, w + 1, 2 * w + 3):
            k = n % w
            case("((_ rotate_left %d) %s)" % (n, X), out(((x << k) | (x >> (w - k))) & m if k else x, w))
            case("((_ rotate_right %d) %s)" % (n, X), out(((x >> k) | (x << (w - k))) & m if k else x, w))
        for n in (1, 2, 3):
            r = 0
            for _ in range(n): r = (r << w) | x
            case("((_ repeat %d) %s)" % (n, X), out(r, w * n))
        hl = {(w - 1, 0), (w - 1, w - 1), (0, 0), (w // 2, w // 2), (w // 2, 0), (w - 1, w // 2)}
        if w == 8:
            hl = {(h, l) for h in range(8) for l in range(h + 1)}
        for h, l in sorted(hl):
            if 0 <= l <= h < w:
                case("((_ extract %d %d) %s)" % (h, l, X), out((x >> l) & ((1 << (h - l + 1)) - 1), h - l + 1))
        for y in V:
            Y = lit(y, w)
            for name, f in (("bvadd", lambda: (x + y) & m), ("bvsub", lambda: (x - y) & m),
                            ("bvmul", lambda: (x * y) & m), ("bvand", lambda: x & y),
                            ("bvor", lambda: x | y), ("bvxor", lambda: x ^ y),
                            ("bvudiv", lambda: udiv(x, y, w)), ("bvurem", lambda: urem(x, y, w)),
                            ("bvsdiv", lambda: sdiv(x, y, w)), ("bvsrem", lambda: srem(x, y, w)),
                            ("bvsmod", lambda: smod(x, y, w))):
                case("(%s %s %s)" % (name, X, Y), out(f(), w))
            for name, f in (("bvule", x <= y), ("bvult", x < y),
                            ("bvsle", sgn(x, w) <= sgn(y, w)), ("bvslt", sgn(x, w) < sgn(y, w)),
                            ("=", x == y)):
                case("(%s %s %s)" % (name, X, Y), b(f))
        for y in sorted({0, 1, 2 % (1 << w), w - 1, w, w + 1, m, 1 << (w - 1)}):
            if y > m: continue
            Y = lit(y, w)
            sh = y if y < w else w
            case("(bvshl %s %s)" % (X, Y), out((x << sh) & m if sh < w else 0, w))
            case("(bvlshr %s %s)" % (X, Y), out(x >> sh if sh < w else 0, w))
            case("(bvashr %s %s)" % (X, Y), out((sgn(x, w) >> sh) & m if sh < w else (m if msb(x, w) else 0), w))
    # concat across widths
for w1, w2 in ((1, 1), (8, 8), (1, 100), (100, 1), (8, 64), (64, 100), (100, 100)):
    for x in values(w1)[:5]:
        for y in values(w2)[:5]:
            case("(concat %s %s)" % (lit(x, w1), lit(y, w2)), out((x << w2) | y, w1 + w2))

open("eval_cases_bv.txt", "w").write(
    "# Generated by gen_eval_cases_bv.py (do not edit by hand). Format: vars ; expr ; expected\n" + "\n".join(lines) + "\n")
print(len(lines), "cases", file=sys.stderr)
