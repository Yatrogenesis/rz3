#!/usr/bin/env python3
# \1MIT OR Apache-2.0
"""Verifiable-by-construction SMT-LIB exercises.

Every instance has a ground truth computed by an independent, solver-free oracle written in
this file (exhaustive search, dynamic programming, exact rational arithmetic, or a theorem).
No SMT solver is consulted to decide a status. The file records the oracle and the status:

    (set-info :status sat|unsat)
    (set-info :source |gen_exercises.py family=<f> seed=<s> oracle=<o>|)

usage: gen_exercises.py <out_dir> [seed] [hard]
Deterministic: the same seed gives byte-identical files (a manifest with SHA-256 is written).
"""
import hashlib
import itertools
import os
import random
import sys
from fractions import Fraction

OUT = sys.argv[1]
SEED = int(sys.argv[2]) if len(sys.argv) > 2 else 20261008
HARD = len(sys.argv) > 3 and sys.argv[3] == 'hard'
os.makedirs(OUT, exist_ok=True)
manifest = []


def emit(name, logic, family, oracle, status, body):
    text = (
        f"(set-info :smt-lib-version 2.6)\n(set-logic {logic})\n"
        f"(set-info :source |gen_exercises.py family={family} seed={SEED} oracle={oracle}|)\n"
        f"(set-info :status {status})\n{body}(check-sat)\n(exit)\n"
    )
    path = os.path.join(OUT, f"{logic}__{family}__{name}.smt2")
    with open(path, "w") as fh:
        fh.write(text)
    manifest.append((os.path.basename(path), logic, family, oracle, status,
                     hashlib.sha256(text.encode()).hexdigest()))


# ---------------------------------------------------------------- pigeonhole (theorem)
def pigeonhole():
    for holes in ((7, 8, 9) if HARD else (3, 4, 5, 6)):
        for pigeons, status in ((holes + 1, "unsat"), (holes, "sat")):
            b = "".join(f"(declare-fun p{i}_{j} () Bool)\n" for i in range(pigeons) for j in range(holes))
            for i in range(pigeons):
                b += "(assert (or " + " ".join(f"p{i}_{j}" for j in range(holes)) + "))\n"
            for j in range(holes):
                for i1 in range(pigeons):
                    for i2 in range(i1 + 1, pigeons):
                        b += f"(assert (not (and p{i1}_{j} p{i2}_{j})))\n"
            emit(f"php_{pigeons}_{holes}", "QF_UF", "pigeonhole", "pigeonhole principle", status, b)


# ---------------------------------------------------------------- n-queens (exhaustive)
def queens_exists(n):
    cols = []

    def go(r, placed):
        if r == n:
            return True
        for c in range(n):
            if all(c != pc and abs(c - pc) != r - pr for pr, pc in placed):
                if go(r + 1, placed + [(r, c)]):
                    return True
        return False

    return go(0, cols)


def queens():
    for n in (range(9, 15) if HARD else range(2, 9)):
        status = "sat" if queens_exists(n) else "unsat"
        b = "".join(f"(declare-fun q{i} () Int)\n" for i in range(n))
        for i in range(n):
            b += f"(assert (and (>= q{i} 0) (< q{i} {n})))\n"
        for i in range(n):
            for j in range(i + 1, n):
                b += f"(assert (distinct q{i} q{j}))\n"
                b += f"(assert (distinct (- q{i} q{j}) {j - i}))\n(assert (distinct (- q{j} q{i}) {j - i}))\n"
        emit(f"queens_{n}", "QF_LIA", "queens", "exhaustive search", status, b)


# ---------------------------------------------------------------- knapsack (dynamic programming)
def knapsack(rng):
    for k in range(10):
        n = rng.randint(20, 32) if HARD else rng.randint(4, 9)
        w = [rng.randint(2, 40 if HARD else 15) for _ in range(n)]
        v = [rng.randint(1, 50 if HARD else 20) for _ in range(n)]
        cap = sum(w) // 2
        best = [0] * (cap + 1)
        for i in range(n):
            for c in range(cap, w[i] - 1, -1):
                best[c] = max(best[c], best[c - w[i]] + v[i])
        opt = best[cap]
        for target, status in ((opt, "sat"), (opt + 1, "unsat")):
            b = "".join(f"(declare-fun x{i} () Int)\n(assert (and (>= x{i} 0) (<= x{i} 1)))\n" for i in range(n))
            b += "(assert (<= (+ " + " ".join(f"(* {w[i]} x{i})" for i in range(n)) + f") {cap}))\n"
            b += "(assert (>= (+ " + " ".join(f"(* {v[i]} x{i})" for i in range(n)) + f") {target}))\n"
            emit(f"knap_{k}_{status}", "QF_LIA", "knapsack", "dynamic programming", status, b)


# ---------------------------------------------------------------- job shop (exhaustive)
def jobshop_opt(durs):
    """durs[j] = list of (machine, duration) in job order. Optimal makespan by exhaustive
    search over machine permutations (semi-active schedules)."""
    machines = sorted({m for job in durs for m, _ in job})
    ops = [(j, o) for j, job in enumerate(durs) for o in range(len(job))]
    best = [10 ** 9]

    def search(next_op, job_ready, mach_ready, scheduled):
        if scheduled == len(ops):
            best[0] = min(best[0], max(job_ready))
            return
        for j in range(len(durs)):
            o = next_op[j]
            if o == len(durs[j]):
                continue
            m, d = durs[j][o]
            start = max(job_ready[j], mach_ready[m])
            jr, mr = job_ready[:], dict(mach_ready)
            jr[j] = mr[m] = start + d
            if max(jr) >= best[0]:
                continue
            no = next_op[:]
            no[j] += 1
            search(no, jr, mr, scheduled + 1)

    search([0] * len(durs), [0] * len(durs), {m: 0 for m in machines}, 0)
    return best[0]


def jobshop(rng):
    for k in range(8):
        nj, nm = (4, 3) if HARD else (rng.randint(2, 3), rng.randint(2, 3))
        durs = []
        for _ in range(nj):
            ms = list(range(nm))
            rng.shuffle(ms)
            durs.append([(m, rng.randint(1, 6)) for m in ms])
        opt = jobshop_opt(durs)
        for span, status in ((opt, "sat"), (opt - 1, "unsat")):
            b = ""
            for j, job in enumerate(durs):
                for o in range(len(job)):
                    b += f"(declare-fun s{j}_{o} () Int)\n(assert (>= s{j}_{o} 0))\n"
                for o in range(len(job) - 1):
                    b += f"(assert (>= s{j}_{o + 1} (+ s{j}_{o} {job[o][1]})))\n"
                b += f"(assert (<= (+ s{j}_{len(job) - 1} {job[-1][1]}) {span}))\n"
            for m in range(nm):
                same = [(j, o, d) for j, job in enumerate(durs) for o, (mm, d) in enumerate(job) if mm == m]
                for (j1, o1, d1), (j2, o2, d2) in itertools.combinations(same, 2):
                    b += (f"(assert (or (>= s{j2}_{o2} (+ s{j1}_{o1} {d1})) "
                          f"(>= s{j1}_{o1} (+ s{j2}_{o2} {d2}))))\n")
            emit(f"js_{k}_{status}", "QF_IDL", "jobshop", "exhaustive schedule search", status, b)


# ---------------------------------------------------------------- bit-vector identities
def bv_identities(rng):
    ids = [
        ("add_xor_and", "(bvadd x y)", "(bvadd (bvxor x y) (bvmul #x{two} (bvand x y)))"),
        ("neg_not", "(bvneg x)", "(bvadd (bvnot x) #x{one})"),
        ("demorgan", "(bvnot (bvand x y))", "(bvor (bvnot x) (bvnot y))"),
        ("sub_neg", "(bvsub x y)", "(bvadd x (bvneg y))"),
        ("or_and_xor", "(bvor x y)", "(bvadd (bvxor x y) (bvand x y))"),
    ]
    for width in ((32, 64) if HARD else (8, 16)):
        hexw = width // 4
        one, two = f"{1:0{hexw}x}", f"{2:0{hexw}x}"
        for name, lhs, rhs in ids:
            r = rhs.format(one=one, two=two)
            decl = f"(declare-fun x () (_ BitVec {width}))\n(declare-fun y () (_ BitVec {width}))\n"
            emit(f"{name}_{width}", "QF_BV", "bv_identity", "algebraic theorem", "unsat",
                 decl + f"(assert (not (= {lhs} {r})))\n")
        # a false identity: exhaustively false witnesses exist for width 8 (checked below)
        wrong = "(bvadd x y)", "(bvor x y)"
        # x=1, y=1 is a witness at every width: 1+1 = 2 != 1|1 = 1
        assert (1 + 1) % (1 << width) != (1 | 1)
        decl = f"(declare-fun x () (_ BitVec {width}))\n(declare-fun y () (_ BitVec {width}))\n"
        emit(f"false_add_or_{width}", "QF_BV", "bv_identity", "explicit counterexample", "sat",
             decl + f"(assert (not (= {wrong[0]} {wrong[1]})))\n")


# ---------------------------------------------------------------- graph colouring (exhaustive)
def colourable(n, edges, k):
    col = [0] * n

    def go(v):
        if v == n:
            return True
        for c in range(k):
            if all(col[u] != c for u, w in edges if w == v and u < v) and all(col[w] != c for u, w in edges if u == v and w < v):
                col[v] = c
                if go(v + 1):
                    return True
        return False

    return go(0)


def colouring(rng):
    for idx in range(10):
        n = rng.randint(22, 30) if HARD else rng.randint(6, 10)
        edges = sorted({tuple(sorted(rng.sample(range(n), 2))) for _ in range(rng.randint(2 * n, 3 * n) if HARD else rng.randint(n, 2 * n + 2))})
        for k in (2, 3):
            status = "sat" if colourable(n, edges, k) else "unsat"
            b = "".join(f"(declare-fun c{i} () Int)\n(assert (and (>= c{i} 0) (< c{i} {k})))\n" for i in range(n))
            b += "".join(f"(assert (distinct c{u} c{v}))\n" for u, v in edges)
            emit(f"col_{idx}_k{k}", "QF_LIA", "colouring", "exhaustive search", status, b)


# ---------------------------------------------------------------- LRA by Fourier-Motzkin (exact)
def fm_feasible(rows, nvars):
    """rows: list of (coeffs tuple of Fraction, op in {'<=','<'}, rhs Fraction). Exact FM."""
    rows = [(list(c), op, r) for c, op, r in rows]
    for var in range(nvars):
        pos, neg, rest = [], [], []
        for c, op, r in rows:
            (pos if c[var] > 0 else neg if c[var] < 0 else rest).append((c, op, r))
        new = list(rest)
        for cp, opp, rp in pos:
            for cn, opn, rn in neg:
                a, b = cp[var], -cn[var]
                c = [cp[i] * b + cn[i] * a for i in range(nvars)]
                new.append((c, "<" if "<" in (opp, opn) else "<=", rp * b + rn * a))
        rows = new
        if len(rows) > 4000:
            return None
    for c, op, r in rows:
        if all(x == 0 for x in c) and (r < 0 or (r == 0 and op == "<")):
            return False
    return True


def lra(rng):
    made = 0
    while made < 24:
        nv, nr = (4, rng.randint(10, 16)) if HARD else (3, rng.randint(4, 8))
        rows = []
        for _ in range(nr):
            c = tuple(Fraction(rng.randint(-4, 4), rng.choice([1, 2, 3])) for _ in range(nv))
            if all(x == 0 for x in c):
                continue
            rows.append((c, rng.choice(["<=", "<"]), Fraction(rng.randint(-6, 6), rng.choice([1, 2]))))
        verdict = fm_feasible(rows, nv)
        if verdict is None:
            continue
        b = "".join(f"(declare-fun v{i} () Real)\n" for i in range(nv))

        def num(f):
            s = f"(/ {abs(f.numerator)}.0 {f.denominator}.0)" if f.denominator != 1 else f"{abs(f.numerator)}.0"
            return f"(- {s})" if f < 0 else s

        for c, op, r in rows:
            lhs = "(+ " + " ".join(f"(* {num(c[i])} v{i})" for i in range(nv)) + ")"
            b += f"(assert ({op} {lhs} {num(r)}))\n"
        emit(f"fm_{made}", "QF_LRA", "lra_fm", "exact Fourier-Motzkin", "sat" if verdict else "unsat", b)
        made += 1


def main():
    rng = random.Random(SEED)
    pigeonhole()
    queens()
    knapsack(rng)
    jobshop(rng)
    bv_identities(rng)
    colouring(rng)
    lra(rng)
    with open(os.path.join(OUT, "MANIFEST.tsv"), "w") as fh:
        fh.write("file\tlogic\tfamily\toracle\tstatus\tsha256\n")
        for row in manifest:
            fh.write("\t".join(row) + "\n")
    print(len(manifest), "instances;",
          {s: sum(1 for m in manifest if m[4] == s) for s in ("sat", "unsat")})


main()
