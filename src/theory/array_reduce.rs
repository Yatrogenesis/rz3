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

    fn add_index(&mut self, ty: &Type, idx: &Expr, lemmas: &mut Vec<Expr>) {
        let list = self.indices.entry(ty.clone()).or_default();
        if list.contains(idx) {
            return;
        }
        list.push(idx.clone());
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
