//! Incremental congruence closure for uninterpreted sorts (EUF), as an online
//! DPLL(T) theory.
//!
//! * Terms are variables and applications of declared functions whose arguments all have
//!   uninterpreted sorts. Boolean-valued applications (predicates) are terms equal to the
//!   distinguished constants `true` / `false`, which are kept apart by an axiom.
//! * Union-find uses union by size and no path compression, so every merge is undone
//!   exactly by popping a trail on backjump.
//! * Explanations come from a spanning forest of the merges: an edge is either an input
//!   equality literal or a congruence step (two applications whose arguments are
//!   pairwise equal), explained recursively (Nieuwenhuis & Oliveras, RTA 2005,
//!   DOI 10.1007/978-3-540-32033-3_33).

use crate::ast::{Expr, Type};
use crate::sat::TheoryHook;
use std::collections::{HashMap, HashSet, VecDeque};

type TermId = u32;

#[derive(Clone, Debug)]
enum Reason {
    /// A literal of the SAT assignment (true under the current assignment).
    Lit(i32),
    /// Congruence between two applications of the same function.
    Cong(TermId, TermId),
}

#[derive(Clone, Debug)]
enum Kind {
    Atom,
    App(u32, Vec<TermId>),
}

#[derive(Clone, Copy, Debug)]
enum AtomKind {
    Eq(TermId, TermId),
    Pred(TermId),
}

enum Undo {
    /// `small` was attached below `large`.
    Union {
        small: TermId,
        large: TermId,
        use_len: usize,
        diseq_len: usize,
    },
    Edge(TermId, TermId),
    Sig(Vec<TermId>, u32, Option<TermId>),
    /// A disequality recorded in the lists of classes `.0` and `.1`.
    Diseq(TermId, TermId),
}

pub struct Cc {
    terms: Vec<Kind>,
    term_ids: HashMap<Expr, TermId>,
    fn_ids: HashMap<String, u32>,
    parent: Vec<TermId>,
    size: Vec<u32>,
    use_list: Vec<Vec<TermId>>,
    sig: HashMap<(u32, Vec<TermId>), TermId>,
    adj: Vec<Vec<(TermId, Reason)>>,
    /// Asserted disequalities `(a, b, literal)`.
    diseqs: Vec<(TermId, TermId, i32)>,
    diseq_by_class: Vec<Vec<usize>>,
    atoms: HashMap<i32, AtomKind>,
    pending: VecDeque<(TermId, TermId, Reason)>,
    trail: Vec<Undo>,
    level_marks: Vec<usize>,
    true_term: TermId,
    false_term: TermId,
    conflict: Option<Vec<i32>>,
    pub conflicts: u64,
}

impl Default for Cc {
    fn default() -> Self {
        Self::new()
    }
}

impl Cc {
    pub fn new() -> Self {
        let mut cc = Cc {
            terms: Vec::new(),
            term_ids: HashMap::new(),
            fn_ids: HashMap::new(),
            parent: Vec::new(),
            size: Vec::new(),
            use_list: Vec::new(),
            sig: HashMap::new(),
            adj: Vec::new(),
            diseqs: Vec::new(),
            diseq_by_class: Vec::new(),
            atoms: HashMap::new(),
            pending: VecDeque::new(),
            trail: Vec::new(),
            level_marks: Vec::new(),
            true_term: 0,
            false_term: 0,
            conflict: None,
            conflicts: 0,
        };
        cc.true_term = cc.new_term(Kind::Atom);
        cc.false_term = cc.new_term(Kind::Atom);
        cc
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    fn new_term(&mut self, kind: Kind) -> TermId {
        let id = self.terms.len() as TermId;
        self.terms.push(kind);
        self.parent.push(id);
        self.size.push(1);
        self.use_list.push(Vec::new());
        self.adj.push(Vec::new());
        self.diseq_by_class.push(Vec::new());
        id
    }

    fn find(&self, mut t: TermId) -> TermId {
        while self.parent[t as usize] != t {
            t = self.parent[t as usize];
        }
        t
    }

    /// Is `ty` a sort handled by this theory?
    pub fn handles_type(ty: &Type) -> bool {
        matches!(ty, Type::Sort(_))
    }

    /// Intern a term; `None` if it contains something this theory does not interpret.
    fn intern(&mut self, e: &Expr) -> Option<TermId> {
        if let Some(&id) = self.term_ids.get(e) {
            return Some(id);
        }
        let id = match e {
            Expr::Var(_, Type::Sort(_)) => self.new_term(Kind::Atom),
            Expr::App(name, args) => {
                let mut ids = Vec::with_capacity(args.len());
                for a in args {
                    ids.push(self.intern(a)?);
                }
                let next = self.fn_ids.len() as u32;
                let f = *self.fn_ids.entry(name.clone()).or_insert(next);
                let id = self.new_term(Kind::App(f, ids.clone()));
                // Register as a parent of its arguments and hash it by signature.
                for &a in &ids {
                    let r = self.find(a);
                    self.use_list[r as usize].push(id);
                }
                let key = (f, ids.iter().map(|&a| self.find(a)).collect::<Vec<_>>());
                match self.sig.get(&key) {
                    Some(&other) => {
                        // Same signature as an existing application: congruent from the start.
                        self.pending.push_back((id, other, Reason::Cong(id, other)));
                    }
                    None => {
                        self.sig.insert(key, id);
                    }
                }
                id
            }
            _ => return None,
        };
        self.term_ids.insert(e.clone(), id);
        Some(id)
    }

    /// Register the atom under SAT variable `var`. Returns false if it is not a CC atom.
    pub fn register(&mut self, var: i32, expr: &Expr) -> bool {
        match expr {
            Expr::Eq(a, b) => {
                let (Some(x), Some(y)) = (self.intern(a), self.intern(b)) else {
                    return false;
                };
                self.atoms.insert(var, AtomKind::Eq(x, y));
                true
            }
            Expr::App(_, _) => {
                let Some(t) = self.intern(expr) else {
                    return false;
                };
                self.atoms.insert(var, AtomKind::Pred(t));
                true
            }
            _ => false,
        }
    }

    fn push_edge(&mut self, a: TermId, b: TermId, reason: Reason) {
        self.adj[a as usize].push((b, reason.clone()));
        self.adj[b as usize].push((a, reason));
        self.trail.push(Undo::Edge(a, b));
    }

    /// Merge classes until the pending queue is empty; stops at the first conflict.
    fn process(&mut self) {
        while self.conflict.is_none() {
            let Some((a, b, reason)) = self.pending.pop_front() else {
                break;
            };
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                continue;
            }
            self.push_edge(a, b, reason);
            let (small, large) = if self.size[ra as usize] < self.size[rb as usize] {
                (ra, rb)
            } else {
                (rb, ra)
            };
            self.trail.push(Undo::Union {
                small,
                large,
                use_len: self.use_list[large as usize].len(),
                diseq_len: self.diseq_by_class[large as usize].len(),
            });
            self.parent[small as usize] = large;
            self.size[large as usize] += self.size[small as usize];

            // Disequalities that now collapse.
            let moved: Vec<usize> = self.diseq_by_class[small as usize].clone();
            for &d in &moved {
                let (x, y, lit) = self.diseqs[d];
                if self.find(x) == self.find(y) {
                    let mut clause = self.explain_eq(x, y);
                    clause.push(-lit);
                    self.fail(clause);
                    return;
                }
            }
            self.diseq_by_class[large as usize].extend(moved);

            // true != false
            if self.find(self.true_term) == self.find(self.false_term) {
                let clause = self.explain_eq(self.true_term, self.false_term);
                self.fail(clause);
                return;
            }

            // Congruence: re-hash the parents of the absorbed class.
            let parents: Vec<TermId> = self.use_list[small as usize].clone();
            for &p in &parents {
                let Kind::App(f, args) = self.terms[p as usize].clone() else {
                    continue;
                };
                let key_args: Vec<TermId> = args.iter().map(|&x| self.find(x)).collect();
                match self.sig.get(&(f, key_args.clone())).copied() {
                    Some(q) if self.find(q) != self.find(p) => {
                        self.pending.push_back((p, q, Reason::Cong(p, q)));
                    }
                    Some(_) => {}
                    None => {
                        self.sig.insert((f, key_args.clone()), p);
                        self.trail.push(Undo::Sig(key_args, f, None));
                    }
                }
            }
            self.use_list[large as usize].extend(parents);
        }
    }

    fn fail(&mut self, clause: Vec<i32>) {
        let mut c = clause;
        c.sort_unstable();
        c.dedup();
        self.conflicts += 1;
        self.conflict = Some(c);
        self.pending.clear();
    }

    /// Literals (all currently true) whose conjunction implies `a = b`.
    fn explain_eq(&self, a: TermId, b: TermId) -> Vec<i32> {
        let mut lits = HashSet::new();
        let mut seen_pairs = HashSet::new();
        self.explain_into(a, b, &mut lits, &mut seen_pairs);
        // Negations: these literals are true, so the conflict clause contains their negations.
        lits.into_iter().map(|l: i32| -l).collect()
    }

    fn explain_into(
        &self,
        a: TermId,
        b: TermId,
        lits: &mut HashSet<i32>,
        seen: &mut HashSet<(TermId, TermId)>,
    ) {
        if a == b || !seen.insert((a.min(b), a.max(b))) {
            return;
        }
        // Path in the spanning forest (a tree per class): BFS from a.
        let mut prev: HashMap<TermId, (TermId, Reason)> = HashMap::new();
        let mut queue = VecDeque::new();
        queue.push_back(a);
        let mut visited: HashSet<TermId> = HashSet::new();
        visited.insert(a);
        while let Some(x) = queue.pop_front() {
            if x == b {
                break;
            }
            for (y, r) in &self.adj[x as usize] {
                if visited.insert(*y) {
                    prev.insert(*y, (x, r.clone()));
                    queue.push_back(*y);
                }
            }
        }
        let mut cur = b;
        while cur != a {
            let Some((p, r)) = prev.get(&cur).cloned() else {
                return; // not connected: nothing to explain
            };
            match r {
                Reason::Lit(l) => {
                    lits.insert(l);
                }
                Reason::Cong(t, u) => {
                    if let (Kind::App(_, ta), Kind::App(_, ua)) =
                        (&self.terms[t as usize], &self.terms[u as usize])
                    {
                        for (x, y) in ta.iter().zip(ua) {
                            self.explain_into(*x, *y, lits, seen);
                        }
                    }
                }
            }
            cur = p;
        }
    }

    fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop() {
                Some(Undo::Union {
                    small,
                    large,
                    use_len,
                    diseq_len,
                }) => {
                    self.size[large as usize] -= self.size[small as usize];
                    self.parent[small as usize] = small;
                    self.use_list[large as usize].truncate(use_len);
                    self.diseq_by_class[large as usize].truncate(diseq_len);
                }
                Some(Undo::Edge(a, b)) => {
                    self.adj[a as usize].pop();
                    self.adj[b as usize].pop();
                }
                Some(Undo::Sig(args, f, old)) => match old {
                    Some(t) => {
                        self.sig.insert((f, args), t);
                    }
                    None => {
                        self.sig.remove(&(f, args));
                    }
                },
                Some(Undo::Diseq(ra, rb)) => {
                    self.diseqs.pop();
                    self.diseq_by_class[ra as usize].pop();
                    self.diseq_by_class[rb as usize].pop();
                }
                None => break,
            }
        }
    }
}

impl TheoryHook for Cc {
    fn new_level(&mut self) {
        self.level_marks.push(self.trail.len());
    }

    fn backtrack(&mut self, level: usize) {
        while self.level_marks.len() > level {
            let mark = self.level_marks.pop().unwrap_or(0);
            self.undo_to(mark);
        }
        self.pending.clear();
        self.conflict = None;
    }

    fn assign(&mut self, lit: i32) -> Result<(), Vec<i32>> {
        let Some(&atom) = self.atoms.get(&lit.abs()) else {
            return Ok(());
        };
        match (atom, lit > 0) {
            (AtomKind::Eq(a, b), true) => self.pending.push_back((a, b, Reason::Lit(lit))),
            (AtomKind::Pred(t), true) => {
                self.pending
                    .push_back((t, self.true_term, Reason::Lit(lit)))
            }
            (AtomKind::Pred(t), false) => {
                self.pending
                    .push_back((t, self.false_term, Reason::Lit(lit)))
            }
            (AtomKind::Eq(a, b), false) => {
                let (ra, rb) = (self.find(a), self.find(b));
                if ra == rb {
                    let mut clause = self.explain_eq(a, b);
                    clause.push(-lit);
                    clause.sort_unstable();
                    clause.dedup();
                    self.conflicts += 1;
                    return Err(clause);
                }
                let d = self.diseqs.len();
                self.diseqs.push((a, b, lit));
                self.diseq_by_class[ra as usize].push(d);
                self.diseq_by_class[rb as usize].push(d);
                self.trail.push(Undo::Diseq(ra, rb));
            }
        }
        Ok(())
    }

    fn check(&mut self) -> Result<Vec<(i32, Vec<i32>)>, Vec<i32>> {
        self.process();
        if let Some(c) = self.conflict.take() {
            return Err(c);
        }
        Ok(Vec::new())
    }
}
