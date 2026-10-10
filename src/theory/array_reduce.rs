//! Reduction of extensional arrays to the theories underneath them.
//!
//! Arrays are removed before the formula reaches the SAT core:
//!
//! * `select(a, i)` over an array variable becomes a fresh element variable `sel(a, i)`,
//!   with the congruence lemma `i = j -> sel(a, i) = sel(a, j)` against every other select
//!   on the same array.
//! * `store(a, i, v)` becomes a fresh array variable `b` with the read-over-write lemmas
//!   `sel(b, i) = v` and, for every index term `j` of the problem,
//!   `j != i -> sel(b, j) = sel(a, j)`.
//! * a constant array `const(v)` becomes a variable `c` with `sel(c, j) = v` for every `j`.
//! * an equality between arrays `a = b` becomes a fresh Boolean `e` together with
//!   `e -> sel(a, j) = sel(b, j)` for every index `j`, and, through a fresh index witness
//!   `k`, `!e -> sel(a, k) != sel(b, k)` (extensionality).
//!
//! The index set grows as terms appear; whenever it grows every source of axioms is
//! instantiated at the new index, and whenever a source appears it is instantiated at every
//! known index. This is the classical complete procedure for the quantifier-free theory of
//! arrays with extensionality over infinite index sorts (Bradley, Manna & Sipma, VMCAI 2006,
//! DOI 10.1007/11609773_28). A work cap turns pathological growth into an `incomplete`
//! flag (never into a wrong answer): the lemmas already produced remain sound.

use crate::ast::{Expr, Type};
use std::collections::BTreeMap;

/// Upper bound on the number of lemmas produced for one solver instance.
const MAX_LEMMAS: usize = 3_000_000;

enum Source {
    Store { b: Expr, a: Expr, i: Expr },
    Const { c: Expr, v: Expr },
    Eq { e: Expr, a: Expr, b: Expr },
}

#[derive(Default)]
pub struct ArrayReducer {
    fresh: usize,
    store_vars: BTreeMap<Expr, Expr>,
    const_vars: BTreeMap<Expr, Expr>,
    sel_vars: BTreeMap<(Expr, Expr), Expr>,
    sels_by_array: BTreeMap<Expr, Vec<(Expr, Expr)>>,
    eq_atoms: BTreeMap<(Expr, Expr), Expr>,
    indices: BTreeMap<Type, Vec<Expr>>,
    /// Per infinite index sort: a fresh index constrained to differ from every other index
    /// term. Instantiating the axioms there captures the "default" behaviour of an array
    /// outside its finitely many explicit indices (needed for constant arrays and
    /// equalities between stores).
    fresh_index: BTreeMap<Type, Expr>,
    sources: Vec<Source>,
    lemma_count: usize,
    /// Instantiation lemmas that are only added when the current model violates them.
    deferred: Vec<Expr>,
    /// The work cap was hit: satisfiable verdicts are no longer trustworthy.
    pub truncated: bool,
}

fn index_type(array: &Type) -> Option<Type> {
    match array {
        Type::Array(i, _) => Some((**i).clone()),
        _ => None,
    }
}

fn element_type(array: &Type) -> Option<Type> {
    match array {
        Type::Array(_, e) => Some((**e).clone()),
        _ => None,
    }
}

fn eq(a: &Expr, b: &Expr) -> Expr {
    Expr::Eq(Box::new(a.clone()), Box::new(b.clone()))
}

fn not(a: Expr) -> Expr {
    Expr::Not(Box::new(a))
}

impl ArrayReducer {
    pub fn new() -> Self {
        Self::default()
    }

    /// (select variables, store/const/equality sources, deferred lemmas, indices)
    pub fn sizes(&self) -> (usize, usize, usize, usize) {
        (
            self.sel_vars.len(),
            self.sources.len(),
            self.deferred.len(),
            self.indices.values().map(|v| v.len()).sum(),
        )
    }

    /// True once any array construct has been seen.
    pub fn active(&self) -> bool {
        self.fresh > 0 || !self.sel_vars.is_empty()
    }

    fn emit(&mut self, lemmas: &mut Vec<Expr>, lemma: Expr) {
        if self.lemma_count >= MAX_LEMMAS {
            self.truncated = true;
            return;
        }
        self.lemma_count += 1;
        lemmas.push(lemma);
    }

    /// A lemma that holds in every model but is only asserted if the current model breaks it.
    fn defer(&mut self, lemma: Expr) {
        if self.lemma_count >= MAX_LEMMAS {
            self.truncated = true;
            return;
        }
        self.lemma_count += 1;
        self.deferred.push(lemma);
    }

    /// Lemmas among the deferred ones that `holds` does not confirm (violated, or not
    /// decidable under the model). They are removed from the pending list: the caller
    /// asserts them for good.
    pub fn take_violated(&mut self, holds: &dyn Fn(&Expr) -> Option<bool>) -> Vec<Expr> {
        let mut violated = Vec::new();
        let mut kept = Vec::with_capacity(self.deferred.len());
        for lemma in std::mem::take(&mut self.deferred) {
            if holds(&lemma) == Some(true) {
                kept.push(lemma);
            } else {
                violated.push(lemma);
            }
        }
        self.deferred = kept;
        violated
    }

    fn name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("__{prefix}_{}", self.fresh)
    }

    /// Reduce every array construct in `expr` (children first); lemmas are appended.
    pub fn reduce(&mut self, expr: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        if matches!(expr, Expr::ForAll(_, _) | Expr::Exists(_, _)) {
            return expr.clone();
        }
        let rebuilt = expr.map_children(&mut |c| self.reduce(c, lemmas));
        match &rebuilt {
            Expr::Select(a, i) => self.select_var(a, i, lemmas),
            Expr::Store(a, i, v) => self.store_var(a, i, v, lemmas),
            Expr::ConstArray(ty, v) => self.const_var(ty, v, lemmas),
            Expr::Eq(a, b) if matches!(a.get_type(), Type::Array(_, _)) => {
                self.array_equality(a, b, lemmas)
            }
            _ => rebuilt,
        }
    }

    /// An index sort with room for an index distinct from any finite set of terms.
    /// Bit-vector widths below 20 are treated as finite: the fresh-index argument does not
    /// hold there, so satisfiable verdicts are withheld.
    fn infinite(ty: &Type) -> Option<bool> {
        match ty {
            Type::Int | Type::Real | Type::Sort(_) => Some(true),
            Type::BitVec(w) => Some(*w >= 20),
            _ => None,
        }
    }

    fn add_index(&mut self, ty: &Type, idx: &Expr, lemmas: &mut Vec<Expr>) {
        if self.indices.get(ty).is_some_and(|l| l.contains(idx)) {
            return;
        }
        if !self.fresh_index.contains_key(ty) {
            match Self::infinite(ty) {
                Some(true) => {
                    let d = Expr::Var(self.name("default"), ty.clone());
                    self.fresh_index.insert(ty.clone(), d.clone());
                    self.indices.entry(ty.clone()).or_default().push(d.clone());
                    for s in 0..self.sources.len() {
                        self.instantiate(s, &d, lemmas);
                    }
                }
                _ => self.truncated = true,
            }
        }
        // The fresh index differs from every explicit index term.
        if let Some(d) = self.fresh_index.get(ty).cloned() {
            self.defer(not(eq(&d, idx)));
        }
        self.indices
            .entry(ty.clone())
            .or_default()
            .push(idx.clone());
        // Instantiate every source of axioms at the new index.
        for s in 0..self.sources.len() {
            self.instantiate(s, idx, lemmas);
        }
    }

    fn known_indices(&self, ty: &Type) -> Vec<Expr> {
        self.indices.get(ty).cloned().unwrap_or_default()
    }

    fn instantiate(&mut self, source: usize, j: &Expr, lemmas: &mut Vec<Expr>) {
        // Clone the pieces first: instantiation creates select variables, which needs `&mut self`.
        enum Piece {
            Store(Expr, Expr, Expr),
            Const(Expr, Expr),
            Eq(Expr, Expr, Expr),
        }
        let piece = match &self.sources[source] {
            Source::Store { b, a, i, .. } => Piece::Store(b.clone(), a.clone(), i.clone()),
            Source::Const { c, v } => Piece::Const(c.clone(), v.clone()),
            Source::Eq { e, a, b, .. } => Piece::Eq(e.clone(), a.clone(), b.clone()),
        };
        match piece {
            Piece::Store(b, a, i) => {
                if j.get_type() != i.get_type() {
                    return;
                }
                let sb = self.select_var(&b, j, lemmas);
                let sa = self.select_var(&a, j, lemmas);
                let _ = &lemmas;
                self.defer(Expr::Or(vec![eq(j, &i), eq(&sb, &sa)]));
            }
            Piece::Const(c, v) => {
                if index_type(&c.get_type()).as_ref() != Some(&j.get_type()) {
                    return;
                }
                let sc = self.select_var(&c, j, lemmas);
                let _ = &lemmas;
                self.defer(eq(&sc, &v));
            }
            Piece::Eq(e, a, b) => {
                if index_type(&a.get_type()).as_ref() != Some(&j.get_type()) {
                    return;
                }
                let sa = self.select_var(&a, j, lemmas);
                let sb = self.select_var(&b, j, lemmas);
                let _ = &lemmas;
                self.defer(Expr::Or(vec![not(e), eq(&sa, &sb)]));
            }
        }
    }

    fn select_var(&mut self, a: &Expr, i: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = (a.clone(), i.clone());
        if let Some(v) = self.sel_vars.get(&key) {
            return v.clone();
        }
        let elem = element_type(&a.get_type()).unwrap_or(Type::Unknown);
        let v = Expr::Var(self.name("sel"), elem);
        let earlier = self.sels_by_array.get(a).cloned().unwrap_or_default();
        for (j, vj) in &earlier {
            if j.get_type() == i.get_type() {
                self.defer(Expr::Or(vec![not(eq(i, j)), eq(&v, vj)]));
            }
        }
        self.sels_by_array
            .entry(a.clone())
            .or_default()
            .push((i.clone(), v.clone()));
        self.sel_vars.insert(key, v.clone());
        if let Some(it) = index_type(&a.get_type()) {
            self.add_index(&it, i, lemmas);
        }
        v
    }

    fn store_var(&mut self, a: &Expr, i: &Expr, v: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = Expr::Store(
            Box::new(a.clone()),
            Box::new(i.clone()),
            Box::new(v.clone()),
        );
        if let Some(b) = self.store_vars.get(&key) {
            return b.clone();
        }
        let b = Expr::Var(self.name("st"), a.get_type());
        self.store_vars.insert(key, b.clone());
        // Read-over-write at the written index.
        let sb = self.select_var(&b, i, lemmas);
        self.emit(lemmas, eq(&sb, v));
        let s = self.sources.len();
        self.sources.push(Source::Store {
            b: b.clone(),
            a: a.clone(),
            i: i.clone(),
        });
        if let Some(it) = index_type(&a.get_type()) {
            for j in self.known_indices(&it) {
                self.instantiate(s, &j, lemmas);
            }
        }
        b
    }

    fn const_var(&mut self, ty: &Type, v: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = Expr::ConstArray(ty.clone(), Box::new(v.clone()));
        if let Some(c) = self.const_vars.get(&key) {
            return c.clone();
        }
        let c = Expr::Var(self.name("const"), ty.clone());
        self.const_vars.insert(key, c.clone());
        let s = self.sources.len();
        self.sources.push(Source::Const {
            c: c.clone(),
            v: v.clone(),
        });
        if let Some(it) = index_type(ty) {
            for j in self.known_indices(&it) {
                self.instantiate(s, &j, lemmas);
            }
        }
        c
    }

    fn array_equality(&mut self, a: &Expr, b: &Expr, lemmas: &mut Vec<Expr>) -> Expr {
        let key = if a <= b {
            (a.clone(), b.clone())
        } else {
            (b.clone(), a.clone())
        };
        if let Some(e) = self.eq_atoms.get(&key) {
            return e.clone();
        }
        let e = Expr::Var(self.name("aeq"), Type::Bool);
        self.eq_atoms.insert(key, e.clone());
        let it = index_type(&a.get_type()).unwrap_or(Type::Unknown);
        let k = Expr::Var(self.name("witness"), it.clone());
        // Extensionality: if the arrays differ, they differ at the witness.
        let sa = self.select_var(a, &k, lemmas);
        let sb = self.select_var(b, &k, lemmas);
        self.emit(lemmas, Expr::Or(vec![e.clone(), not(eq(&sa, &sb))]));
        let s = self.sources.len();
        self.sources.push(Source::Eq {
            e: e.clone(),
            a: a.clone(),
            b: b.clone(),
        });
        for j in self.known_indices(&it) {
            self.instantiate(s, &j, lemmas);
        }
        e
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arr(i: Type, e: Type) -> Type {
        Type::Array(Box::new(i), Box::new(e))
    }
    fn a(name: &str) -> Expr {
        Expr::Var(name.to_string(), arr(Type::Int, Type::Int))
    }
    fn iv(name: &str) -> Expr {
        Expr::Var(name.to_string(), Type::Int)
    }
    fn sel(arr: Expr, i: Expr) -> Expr {
        Expr::Select(Box::new(arr), Box::new(i))
    }

    #[test]
    fn fresh_reducer_is_inactive_and_empty() {
        let r = ArrayReducer::new();
        assert_eq!(r.sizes(), (0, 0, 0, 0));
        assert!(!r.active());
        assert!(!r.truncated);
    }

    #[test]
    fn select_becomes_a_named_variable_with_a_default_index() {
        let mut r = ArrayReducer::new();
        let mut lemmas = Vec::new();
        let out = r.reduce(&sel(a("a"), iv("i")), &mut lemmas);
        assert_eq!(out, Expr::Var("__sel_1".to_string(), Type::Int));
        assert!(lemmas.is_empty(), "read lemmas are deferred, not emitted");
        // One select; the default index and `i` are known; default != i is deferred.
        assert_eq!(r.sizes(), (1, 0, 1, 2));
        assert!(r.active());
        assert!(!r.truncated);
        // The same select is shared; a second index adds a select, a congruence lemma
        // and a disequality with the default.
        assert_eq!(r.reduce(&sel(a("a"), iv("i")), &mut lemmas), out);
        let out2 = r.reduce(&sel(a("a"), iv("j")), &mut lemmas);
        assert_eq!(out2, Expr::Var("__sel_3".to_string(), Type::Int));
        assert_eq!(r.sizes(), (2, 0, 3, 3));
    }

    #[test]
    fn deferred_lemmas_are_released_only_when_the_model_does_not_confirm_them() {
        let build = || {
            let mut r = ArrayReducer::new();
            let mut l = Vec::new();
            r.reduce(&sel(a("a"), iv("i")), &mut l);
            r
        };
        let mut r = build();
        assert!(r.take_violated(&|_| Some(true)).is_empty());
        assert_eq!(r.sizes().2, 1, "confirmed lemmas stay pending");
        let mut r = build();
        let v = r.take_violated(&|_| Some(false));
        assert_eq!(v.len(), 1);
        assert_eq!(r.sizes().2, 0, "released lemmas leave the pending list");
        let mut r = build();
        assert_eq!(r.take_violated(&|_| None).len(), 1);
        assert_eq!(r.sizes().2, 0);
        // The released lemma is default != i.
        let mut r = build();
        let v = r.take_violated(&|_| None);
        assert_eq!(
            v,
            vec![Expr::Not(Box::new(Expr::Eq(
                Box::new(Expr::Var("__default_2".to_string(), Type::Int)),
                Box::new(iv("i"))
            )))]
        );
    }

    #[test]
    fn infinite_index_sorts() {
        assert_eq!(ArrayReducer::infinite(&Type::Int), Some(true));
        assert_eq!(ArrayReducer::infinite(&Type::Real), Some(true));
        assert_eq!(
            ArrayReducer::infinite(&Type::Sort("S".to_string())),
            Some(true)
        );
        assert_eq!(ArrayReducer::infinite(&Type::BitVec(20)), Some(true));
        assert_eq!(ArrayReducer::infinite(&Type::BitVec(64)), Some(true));
        assert_eq!(ArrayReducer::infinite(&Type::BitVec(19)), Some(false));
        assert_eq!(ArrayReducer::infinite(&Type::BitVec(1)), Some(false));
        assert_eq!(ArrayReducer::infinite(&Type::Bool), None);
    }

    #[test]
    fn finite_index_sorts_withhold_satisfiable_verdicts() {
        // Bit-vector index of width 8: no fresh default index, and the reducer says so.
        let bv8 = Type::BitVec(8);
        let arr8 = Expr::Var("m".to_string(), arr(bv8.clone(), Type::Int));
        let mut r = ArrayReducer::new();
        let mut l = Vec::new();
        r.reduce(&sel(arr8, Expr::Var("k".to_string(), bv8)), &mut l);
        assert!(r.truncated);
        assert_eq!(r.sizes(), (1, 0, 0, 1));
        // Wide bit-vectors and integers are not truncated.
        let bv32 = Type::BitVec(32);
        let arr32 = Expr::Var("m".to_string(), arr(bv32.clone(), Type::Int));
        let mut r = ArrayReducer::new();
        r.reduce(&sel(arr32, Expr::Var("k".to_string(), bv32)), &mut l);
        assert!(!r.truncated);
        assert_eq!(r.sizes(), (1, 0, 1, 2));
    }

    #[test]
    fn store_emits_read_over_write_and_defers_the_frame_lemmas() {
        let mut r = ArrayReducer::new();
        let mut lemmas = Vec::new();
        let st = Expr::Store(Box::new(a("a")), Box::new(iv("i")), Box::new(iv("v")));
        let out = r.reduce(&st, &mut lemmas);
        assert_eq!(
            out,
            Expr::Var("__st_1".to_string(), arr(Type::Int, Type::Int))
        );
        // sel(b, i) = v, emitted immediately.
        assert_eq!(
            lemmas,
            vec![Expr::Eq(
                Box::new(Expr::Var("__sel_2".to_string(), Type::Int)),
                Box::new(iv("v"))
            )]
        );
        assert_eq!(r.sizes().1, 1);
        assert!(r.active());
        // The same store is shared.
        assert_eq!(r.reduce(&st, &mut lemmas), out);
        assert_eq!(lemmas.len(), 1);
    }

    #[test]
    fn constant_array_alone_makes_the_reducer_active() {
        let mut r = ArrayReducer::new();
        let mut l = Vec::new();
        let c = Expr::ConstArray(arr(Type::Int, Type::Int), Box::new(Expr::Int(0)));
        let out = r.reduce(&c, &mut l);
        assert_eq!(
            out,
            Expr::Var("__const_1".to_string(), arr(Type::Int, Type::Int))
        );
        assert_eq!(r.sizes(), (0, 1, 0, 0));
        assert!(r.active());
        assert_eq!(r.reduce(&c, &mut l), out);
    }

    #[test]
    fn array_equality_is_symmetric_and_names_a_boolean() {
        let mut r = ArrayReducer::new();
        let mut l = Vec::new();
        let ab = Expr::Eq(Box::new(a("a")), Box::new(a("b")));
        let ba = Expr::Eq(Box::new(a("b")), Box::new(a("a")));
        let e1 = r.reduce(&ab, &mut l);
        let e2 = r.reduce(&ba, &mut l);
        assert_eq!(e1, e2);
        assert!(matches!(&e1, Expr::Var(n, Type::Bool) if n.starts_with("__aeq_")));
        // Extensionality: e or sel(a,k) != sel(b,k).
        assert_eq!(l.len(), 1);
        assert!(matches!(&l[0], Expr::Or(v) if v.len() == 2 && v[0] == e1));
        assert_eq!(r.sizes().1, 1);
        // Equality of non-array terms is untouched.
        let plain = Expr::Eq(Box::new(iv("x")), Box::new(iv("y")));
        assert_eq!(r.reduce(&plain, &mut l), plain);
    }
}
