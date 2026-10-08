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
        self.W = rng.choice([1, 2, 5, 8, 16, 33, 64])
        self.incr = False
        if profile == "incr":
            # the incremental driver draws its formulas from one of the other generators
            self.profile = rng.choice(["lia", "lra", "diff", "uf", "bv", "mixed", "bvw", "sorts", "arr", "arrsort", "quant", "nra", "nia"])
            self.incr = True

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
        if k < 0.93:
            return f"(let ((t {self.int_term(d-1)})) (+ t {r.choice(['t','1','a'])}))"
        if k < 0.955:
            return f"(div {self.int_term(d-1)} {r.choice(['2','3','-2','5'])})"
        if k < 0.97:
            return f"(mod {self.int_term(d-1)} {r.choice(['2','3','-3','4'])})"
        if k < 0.985:
            return f"(abs {self.int_term(d-1)})"
        if k < 0.995 and self.profile in ("mixed", "lra"):
            return f"(to_int {self.real_term(d-1)})"
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
        if k < 0.92:
            return f"(to_real {self.int_term(d-1)})"
        return f"(ite {self.bool_term(d-1)} {self.real_term(d-1)} {self.real_term(d-1)})"

    def bv_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return r.choice(["p", "q", "s", f"#x{r.randint(0, 255):02x}", f"#b{r.randint(0, 255):08b}", f"(_ bv{r.randint(0,255)} 8)"])
        k = r.random()
        two = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvlshr", "bvashr"]
        if k < 0.65:
            return f"({r.choice(two)} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        if k < 0.70:
            return f"(bvnot {self.bv_term(d-1)})"
        if k < 0.76:
            op = r.choice(["bvneg", "bvnand", "bvnor", "bvxnor"])
            if op == "bvneg":
                return f"(bvneg {self.bv_term(d-1)})"
            return f"({op} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        if k < 0.82:
            return f"({r.choice(['bvudiv','bvurem','bvsdiv','bvsrem','bvsmod'])} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        if k < 0.85:
            return f"(concat ((_ extract 3 0) {self.bv_term(d-1)}) ((_ extract 7 4) {self.bv_term(d-1)}))"
        if k < 0.90:
            return f"(ite {self.bool_term(d-1)} {self.bv_term(d-1)} {self.bv_term(d-1)})"
        if k < 0.95:
            return r.choice([
                f"((_ extract 7 0) ((_ zero_extend 3) {self.bv_term(d-1)}))",
                f"((_ extract 7 0) ((_ sign_extend 5) {self.bv_term(d-1)}))",
                f"((_ rotate_left {r.randint(0,10)}) {self.bv_term(d-1)})",
                f"((_ rotate_right {r.randint(0,10)}) {self.bv_term(d-1)})",
                f"((_ extract 7 0) ((_ repeat 2) {self.bv_term(d-1)}))",
            ])
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
        if k == "bool" and self.profile in ("mixed", "lra") and r.random() < 0.15:
            return f"(is_int {self.real_term(max(d-1,0))})"
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

    # --- variable-width bit-vectors ---
    def bvw_const(self):
        w = self.W
        r = self.r
        pick = r.random()
        if pick < 0.25:
            v = 0
        elif pick < 0.4:
            v = (1 << w) - 1
        elif pick < 0.5:
            v = 1 << (w - 1)
        else:
            v = r.getrandbits(w)
        return f"(_ bv{v} {w})"

    def bvw_term(self, d):
        r = self.r
        w = self.W
        if d <= 0 or r.random() < 0.25:
            return r.choice(["u", "v", "t", self.bvw_const(), self.bvw_const()])
        k = r.random()
        two = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvshl", "bvlshr", "bvashr"]
        if k < 0.6:
            return f"({r.choice(two)} {self.bvw_term(d-1)} {self.bvw_term(d-1)})"
        if k < 0.66:
            return f"(bvnot {self.bvw_term(d-1)})"
        if k < 0.72:
            op = r.choice(["bvneg", "bvnand", "bvnor", "bvxnor"])
            if op == "bvneg":
                return f"(bvneg {self.bvw_term(d-1)})"
            return f"({op} {self.bvw_term(d-1)} {self.bvw_term(d-1)})"
        if k < 0.78:
            return f"({r.choice(['bvudiv','bvurem','bvsdiv','bvsrem','bvsmod'])} {self.bvw_term(d-1)} {self.bvw_term(d-1)})"
        if k < 0.82:
            return r.choice([
                f"((_ extract {w-1} 0) ((_ zero_extend {r.randint(1,4)}) {self.bvw_term(d-1)}))",
                f"((_ extract {w-1} 0) ((_ sign_extend {r.randint(1,4)}) {self.bvw_term(d-1)}))",
                f"((_ rotate_left {r.randint(0,70)}) {self.bvw_term(d-1)})",
                f"((_ rotate_right {r.randint(0,70)}) {self.bvw_term(d-1)})",
                f"((_ extract {w-1} 0) ((_ repeat 2) {self.bvw_term(d-1)}))",
            ]) if w <= 32 else f"(bvnot {self.bvw_term(d-1)})"
        if k < 0.86 and w >= 2:
            h = r.randint(0, w - 2)
            return (f"(concat ((_ extract {h} 0) {self.bvw_term(d-1)}) "
                    f"((_ extract {w-1} {h+1}) {self.bvw_term(d-1)}))")
        if k < 0.9:
            return f"(ite {self.bvw_atom(d-1)} {self.bvw_term(d-1)} {self.bvw_term(d-1)})"
        return f"((_ extract {w-1} 0) {self.bvw_term(d-1)})"

    def bvw_atom(self, d):
        op = self.r.choice(["=", "distinct", "bvult", "bvule", "bvslt", "bvsle", "bvugt", "bvuge", "bvsgt", "bvsge", "bvcomp"])
        if op == "bvcomp":
            return f"(= (bvcomp {self.bvw_term(d)} {self.bvw_term(d)}) #b1)"
        return f"({op} {self.bvw_term(d)} {self.bvw_term(d)})"

    def bvw_formula(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.4:
            return self.bvw_atom(max(d, 1))
        k = r.random()
        if k < 0.35:
            return f"(and {self.bvw_formula(d-1)} {self.bvw_formula(d-1)})"
        if k < 0.7:
            return f"(or {self.bvw_formula(d-1)} {self.bvw_formula(d-1)})"
        if k < 0.85:
            return f"(not {self.bvw_formula(d-1)})"
        return f"(=> {self.bvw_formula(d-1)} {self.bvw_formula(d-1)})"

    # --- uninterpreted sorts ---
    def sort_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.4:
            return r.choice(["s1", "s2", "s3", "s4"])
        k = r.random()
        if k < 0.6:
            return f"(g {self.sort_term(d-1)})"
        if k < 0.85:
            return f"(kk {self.sort_term(d-1)} {self.sort_term(d-1)})"
        return f"(ite {self.sort_atom(d-1)} {self.sort_term(d-1)} {self.sort_term(d-1)})"

    def sort_atom(self, d):
        r = self.r
        k = r.random()
        if k < 0.5:
            return f"(= {self.sort_term(d)} {self.sort_term(d)})"
        if k < 0.65:
            return f"(distinct {self.sort_term(d)} {self.sort_term(d)} {self.sort_term(d)})"
        if k < 0.85:
            return f"(pp {self.sort_term(d)})"
        return r.choice(["m", "n"])

    def sort_formula(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.35:
            return self.sort_atom(max(d, 1))
        k = r.random()
        if k < 0.35:
            return f"(and {self.sort_formula(d-1)} {self.sort_formula(d-1)})"
        if k < 0.7:
            return f"(or {self.sort_formula(d-1)} {self.sort_formula(d-1)})"
        if k < 0.85:
            return f"(not {self.sort_formula(d-1)})"
        return f"(=> {self.sort_formula(d-1)} {self.sort_formula(d-1)})"

    # --- arrays (Int -> Int) and arrays over uninterpreted sorts ---
    def arr_index(self, d):
        r = self.r
        if self.profile == "arrsort":
            return r.choice(["i1", "i2", "i3"])
        if d <= 0 or r.random() < 0.5:
            return r.choice(["a", "b", "c", str(r.randint(0, 3))])
        return f"(+ {self.arr_index(d-1)} {r.choice(['1','2','(- 1)'])})"

    def arr_elem(self, d):
        r = self.r
        if self.profile == "arrsort":
            return r.choice(["e1", "e2", "e3"])
        if d <= 0 or r.random() < 0.5:
            return r.choice(["a", "b", str(r.randint(0, 4))])
        return f"(+ {self.arr_elem(d-1)} {r.choice(['1','2'])})"

    def arr_term(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.35:
            return r.choice(["A", "B", "C"])
        k = r.random()
        if k < 0.7:
            return f"(store {self.arr_term(d-1)} {self.arr_index(1)} {self.arr_elem(1)})"
        if k < 0.82 and self.profile == "arr":
            return f"((as const (Array Int Int)) {r.randint(0, 3)})"
        return f"(ite {self.arr_atom(d-1)} {self.arr_term(d-1)} {self.arr_term(d-1)})"

    def arr_val(self, d):
        return f"(select {self.arr_term(d)} {self.arr_index(1)})"

    def arr_atom(self, d):
        r = self.r
        k = r.random()
        if k < 0.35:
            return f"(= {self.arr_term(d)} {self.arr_term(d)})"
        if k < 0.55:
            return f"(= {self.arr_val(d)} {self.arr_elem(1)})"
        if k < 0.75:
            return f"(= {self.arr_val(d)} {self.arr_val(d)})"
        if k < 0.88 and self.profile == "arr":
            return f"({r.choice(['<','<=','>'])} {self.arr_val(d)} {self.arr_val(d)})"
        if k < 0.94:
            return f"(= {self.arr_index(1)} {self.arr_index(1)})"
        return r.choice(["m", "n"])

    def arr_formula(self, d):
        r = self.r
        if d <= 0 or r.random() < 0.35:
            return self.arr_atom(max(d, 1))
        k = r.random()
        if k < 0.35:
            return f"(and {self.arr_formula(d-1)} {self.arr_formula(d-1)})"
        if k < 0.7:
            return f"(or {self.arr_formula(d-1)} {self.arr_formula(d-1)})"
        if k < 0.85:
            return f"(not {self.arr_formula(d-1)})"
        return f"(=> {self.arr_formula(d-1)} {self.arr_formula(d-1)})"

    # --- quantifiers over Int with an uninterpreted function and predicate ---
    def q_term(self, d, bound):
        r = self.r
        pool = bound + ["a", "b", "0", "1", "2"]
        if d <= 0 or r.random() < 0.45:
            return r.choice(pool)
        k = r.random()
        if k < 0.35:
            return f"(f {self.q_term(d-1, bound)})"
        if k < 0.6:
            return f"(+ {self.q_term(d-1, bound)} {self.q_term(d-1, bound)})"
        if k < 0.8:
            return f"(- {self.q_term(d-1, bound)} {self.q_term(d-1, bound)})"
        return f"(* {r.randint(-2, 3)} {self.q_term(d-1, bound)})"

    def q_atom(self, d, bound):
        r = self.r
        k = r.random()
        if k < 0.55:
            op = r.choice(["=", "<", "<=", ">", ">="])
            return f"({op} {self.q_term(d, bound)} {self.q_term(d, bound)})"
        if k < 0.8:
            return f"(pq {self.q_term(d, bound)})"
        return r.choice(["m", "n"])

    def q_formula(self, d, bound):
        r = self.r
        if d <= 0 or r.random() < 0.3:
            return self.q_atom(1, bound)
        k = r.random()
        if k < 0.25:
            return f"(and {self.q_formula(d-1, bound)} {self.q_formula(d-1, bound)})"
        if k < 0.45:
            return f"(or {self.q_formula(d-1, bound)} {self.q_formula(d-1, bound)})"
        if k < 0.55:
            return f"(not {self.q_formula(d-1, bound)})"
        if k < 0.65:
            return f"(=> {self.q_formula(d-1, bound)} {self.q_formula(d-1, bound)})"
        v = f"x{len(bound)}"
        q = r.choice(["forall", "forall", "exists"])
        return f"({q} (({v} Int)) {self.q_formula(d-1, bound + [v])})"

    # --- nonlinear arithmetic (reals and integers) ---
    def nl_term(self, d, ints):
        r = self.r
        vs = ["i", "j", "k2"] if ints else ["x", "y", "z"]
        if d <= 0 or r.random() < 0.3:
            return r.choice(vs + [str(r.randint(-3, 4)) if ints else f"{r.randint(-3, 4)}.0"])
        k = r.random()
        if k < 0.35:
            return f"(* {self.nl_term(d-1, ints)} {self.nl_term(d-1, ints)})"
        if k < 0.55:
            return f"(+ {self.nl_term(d-1, ints)} {self.nl_term(d-1, ints)})"
        if k < 0.7:
            return f"(- {self.nl_term(d-1, ints)} {self.nl_term(d-1, ints)})"
        if k < 0.82:
            c = r.randint(-2, 3)
            return f"(* {c if ints else str(c) + '.0'} {self.nl_term(d-1, ints)})"
        if k < 0.93:
            # division by terms that may be zero or non-constant (unspecified at zero in SMT-LIB)
            op = r.choice(["div", "mod"]) if ints else "/"
            return f"({op} {self.nl_term(d-1, ints)} {self.nl_term(d-1, ints)})"
        return f"(* {r.choice(vs)} {r.choice(vs)})"

    def nl_atom(self, d, ints):
        op = self.r.choice(["<", "<=", ">", ">=", "="])
        return f"({op} {self.nl_term(d, ints)} {self.nl_term(d, ints)})"

    def nl_formula(self, d, ints):
        r = self.r
        if d <= 0 or r.random() < 0.4:
            return self.nl_atom(2, ints)
        k = r.random()
        if k < 0.5:
            return f"(and {self.nl_formula(d-1, ints)} {self.nl_formula(d-1, ints)})"
        if k < 0.85:
            return f"(or {self.nl_formula(d-1, ints)} {self.nl_formula(d-1, ints)})"
        return f"(not {self.nl_formula(d-1, ints)})"

    def declarations(self):
        lines = ["(set-logic ALL)"]
        if self.profile in ("nra", "nia"):
            if self.profile == "nra":
                lines += [f"(declare-fun {v} () Real)" for v in "xyz"]
            else:
                lines += [f"(declare-fun {v} () Int)" for v in ("i", "j", "k2")]
            return lines
        if self.profile == "quant":
            lines += [f"(declare-fun {v} () Int)" for v in "ab"]
            lines += [f"(declare-fun {v} () Bool)" for v in "mn"]
            lines += ["(declare-fun f (Int) Int)", "(declare-fun pq (Int) Bool)"]
            return lines
        if self.profile in ("arr", "arrsort"):
            if self.profile == "arrsort":
                lines += ["(declare-sort I 0)", "(declare-sort E 0)"]
                lines += [f"(declare-fun i{k} () I)" for k in (1, 2, 3)]
                lines += [f"(declare-fun e{k} () E)" for k in (1, 2, 3)]
                lines += [f"(declare-fun {v} () (Array I E))" for v in "ABC"]
            else:
                lines += [f"(declare-fun {v} () Int)" for v in "abc"]
                lines += [f"(declare-fun {v} () (Array Int Int))" for v in "ABC"]
            lines += [f"(declare-fun {v} () Bool)" for v in "mn"]
            return lines
        if self.profile == "sorts":
            lines += ["(declare-sort U 0)"]
            lines += [f"(declare-fun s{i} () U)" for i in range(1, 5)]
            lines += [f"(declare-fun {v} () Bool)" for v in "mn"]
            lines += ["(declare-fun g (U) U)", "(declare-fun kk (U U) U)", "(declare-fun pp (U) Bool)"]
            return lines
        lines += [f"(declare-fun {v} () Int)" for v in "abc"]
        lines += [f"(declare-const {v} Real)" for v in "xyz"]
        lines += [f"(declare-fun {v} () (_ BitVec 8))" for v in "pqs"]
        if self.profile == "bvw":
            lines += [f"(declare-fun {v} () (_ BitVec {self.W}))" for v in "uvt"]
        lines += [f"(declare-fun {v} () Bool)" for v in "mno"]
        lines += ["(declare-fun f (Int) Int)", "(declare-fun pr (Int) Bool)"]
        return lines

    def one_assertion(self, depth):
        if self.profile in ("nra", "nia"):
            return f"(assert {self.nl_formula(depth, self.profile == 'nia')})"
        if self.profile == "quant":
            return f"(assert {self.q_formula(depth, [])})"
        if self.profile in ("arr", "arrsort"):
            return f"(assert {self.arr_formula(depth)})"
        if self.profile == "sorts":
            return f"(assert {self.sort_formula(depth)})"
        if self.profile == "bvw":
            return f"(assert {self.bvw_formula(depth)})"
        return f"(assert {self.bool_term(depth)})"

    def incremental_script(self):
        """Several check-sats with push/pop interleaved, to exercise solver state reuse."""
        r = self.r
        lines = self.declarations()
        depth = 0
        for _ in range(r.randint(1, 3)):
            lines.append(self.one_assertion(r.randint(1, 3)))
        lines.append("(check-sat)")
        for _ in range(r.randint(2, 5)):
            k = r.random()
            if k < 0.3:
                lines.append("(push 1)")
                depth += 1
            elif k < 0.5 and depth > 0:
                lines.append("(pop 1)")
                depth -= 1
            else:
                lines.append(self.one_assertion(r.randint(1, 3)))
            if r.random() < 0.6:
                lines.append("(check-sat)")
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"

    def script(self):
        r = self.r
        if self.incr:
            return self.incremental_script()
        lines = self.declarations()
        if r.random() < 0.3:
            lines.append(f"(define-fun k () Int {r.randint(-2, 5)})")
            lines.append("(define-fun dbl ((u2 Int)) Int (+ u2 u2))")
            if self.profile in ("lia", "mixed"):
                lines.append("(assert (> (dbl a) k))")
        boost = int(os.environ.get("FUZZ_BOOST", "0"))
        for _ in range(r.randint(1, 4 + boost)):
            lines.append(self.one_assertion(r.randint(1, 3 + boost)))
        lines.append("(check-sat)")
        return "\n".join(lines) + "\n"


def run(bin_args, path):
    try:
        p = subprocess.run(bin_args + [path], capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout", [], ""
    out = p.stdout.strip()
    toks = [t for t in out.split() if t in ("sat", "unsat", "unknown")]
    if "panicked" in p.stderr or p.returncode < 0:
        return "crash", toks, p.stderr[:200]
    if "(error" in out and not toks:
        return "error", toks, out[:200]
    return ("ok" if toks else "none"), toks, out[:200]


def one(i):
    rng = random.Random(SEED * 1_000_003 + i)
    profile = rng.choice(["lia", "lra", "diff", "uf", "bv", "mixed", "bvw", "sorts", "arr", "arrsort", "quant", "nra", "nia", "incr"])
    text = Gen(rng, profile).script()
    path = os.path.join(OUT, f"case_{i}.smt2")
    with open(path, "w") as fh:
        fh.write(text)
    sa, ta, ad = run([RZ3], path)
    sb, tb, bd = run([Z3, "-smt2", "smt.random_seed=0"], path)
    # first position where both are decisive and differ
    disagree = any(x in ("sat", "unsat") and y in ("sat", "unsat") and x != y for x, y in zip(ta, tb))
    if disagree:
        a, b = "DISAGREE", "DISAGREE"
    elif sa in ("crash", "timeout", "none"):
        a, b = sa, "-"
    elif sa == "error" and tb:
        a, b = "error", "-"
    elif sb != "ok":
        a, b = "ok", f"z3:{sb}"
    elif len(ta) != len(tb):
        a, b = "COUNT", "-"
    elif ta == tb:
        a, b = "same", "same"
    else:
        a, b = "declined", "-"
    return i, profile, a, b, path, ad, bd


def main():
    os.makedirs(OUT, exist_ok=True)
    stats = {}
    bad = []
    with ThreadPoolExecutor(max_workers=3) as ex:
        for i, profile, a, b, path, ad, bd in ex.map(one, range(N)):
            stats[(profile, a if not b.startswith("z3:") else b)] = stats.get((profile, a if not b.startswith("z3:") else b), 0) + 1
            if a == "DISAGREE":
                bad.append({"case": path, "profile": profile, "kind": "disagreement"})
            elif a in ("crash", "timeout", "none", "error", "COUNT"):
                bad.append({"case": path, "profile": profile, "kind": a, "detail": ad[:150]})
            elif a == "same" and not os.environ.get("FUZZ_KEEP"):
                os.remove(path)
    summary = {}
    for (profile, a), n in sorted(stats.items()):
        summary.setdefault(profile, {})[a] = n
    dis = [x for x in bad if x["kind"] == "disagreement"]
    oth = [x for x in bad if x["kind"] != "disagreement"]
    print(json.dumps({"n": N, "seed": SEED, "summary": summary,
                      "disagreements": dis, "crashes_or_errors": oth[:20],
                      "n_disagreements": len(dis), "n_crash_or_error": len(oth)}, indent=1))


main()
