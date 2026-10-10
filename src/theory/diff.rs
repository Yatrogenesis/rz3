//! Difference-logic accelerator (Cotton & Maler, SAT 2006, DOI 10.1007/11814948_18).
//!
//! Atoms of the shape `x - y <op> c` (or `x <op> c`, with `y` the zero node) are kept as edges
//! of a weighted graph: `x - y <= c` is the edge `y -> x` of weight `c`. A feasible
//! assignment of potentials is maintained incrementally; adding an edge that violates it
//! triggers a Dijkstra-style repair on reduced costs, and reaching the tail of the new edge
//! means a negative cycle, i.e. a conflict whose clause is the cycle's literals.
//!
//! After each edge, shortest paths through it decide *unassigned* atoms (theory
//! propagation): if a path of weight `<= c` already joins the ends of an atom's edge, the
//! atom is implied, with the path's literals as reason.
//!
//! The simplex stays the authority on consistency and models of the whole arithmetic problem;
//! everything reported here (conflicts, implications) is valid for any superset of the
//! constraints, so combining the two is sound.

use super::qnum::{D, Q};
use crate::sat::TheoryHook;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DlOp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

/// A registered difference atom: `u - v <op> bound` (`v` absent means `u <op> bound`).
#[derive(Clone, Debug)]
pub struct DlAtom {
    pub lit: i32,
    pub u: u32,
    pub v: Option<u32>,
    pub op: DlOp,
    pub bound: Q,
    pub int_row: bool,
}

#[derive(Clone, Debug)]
struct Edge {
    from: u32,
    to: u32,
    w: D,
    lit: i32,
}

struct Atom {
    lit: i32,
    /// Edges that hold when the atom is true / false.
    pos: Vec<(u32, u32, D)>,
    neg: Vec<(u32, u32, D)>,
}

pub struct DiffLogic {
    node_of: HashMap<u32, u32>,
    pot: Vec<D>,
    out: Vec<Vec<u32>>,
    inn: Vec<Vec<u32>>,
    edges: Vec<Edge>,
    atoms: Vec<Atom>,
    atom_of_var: HashMap<i32, usize>,
    truth: Vec<Option<bool>>,
    /// Per source node, `(atom, polarity)` whose single implied edge starts there.
    alt_from: Vec<Vec<(usize, bool)>>,
    asserted: Vec<usize>,
    level_marks: Vec<(usize, usize)>,
    pending: Vec<(i32, Vec<i32>)>,
    pub conflicts: u64,
    pub propagations: u64,
    /// Experimental: off unless enabled (measured: no gain on the SMT-LIB dev instances).
    pub enabled: bool,
    /// Run theory propagation (set by the solver when every arithmetic atom is a difference).
    pub propagate: bool,
    pub time_ns: u128,
    pub repair_ns: u128,
    pub search_ns: u128,
}

impl Default for DiffLogic {
    fn default() -> Self {
        Self::new()
    }
}

impl DiffLogic {
    pub fn new() -> Self {
        let mut d = DiffLogic {
            node_of: HashMap::new(),
            pot: Vec::new(),
            out: Vec::new(),
            inn: Vec::new(),
            edges: Vec::new(),
            atoms: Vec::new(),
            atom_of_var: HashMap::new(),
            truth: Vec::new(),
            alt_from: Vec::new(),
            asserted: Vec::new(),
            level_marks: Vec::new(),
            pending: Vec::new(),
            conflicts: 0,
            propagations: 0,
            enabled: false,
            propagate: false,
            time_ns: 0,
            repair_ns: 0,
            search_ns: 0,
        };
        d.new_node(); // node 0 is the zero node
        d
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    fn new_node(&mut self) -> u32 {
        self.pot.push(D::zero());
        self.out.push(Vec::new());
        self.inn.push(Vec::new());
        self.alt_from.push(Vec::new());
        (self.pot.len() - 1) as u32
    }

    fn node(&mut self, var: u32) -> u32 {
        if let Some(&n) = self.node_of.get(&var) {
            return n;
        }
        let n = self.new_node();
        self.node_of.insert(var, n);
        n
    }

    /// `x - y <= w` as an edge `y -> x`.
    fn le(x: u32, y: u32, w: D) -> (u32, u32, D) {
        (y, x, w)
    }

    pub fn register(&mut self, a: &DlAtom) {
        let x = self.node(a.u);
        let y = a.v.map_or(0, |v| self.node(v));
        let b = &a.bound;
        let b_d = D::exact(b.clone());
        let nb_d = D::exact(b.neg());
        let strict = |q: &Q| D::new(q.clone(), Q::from_i64(-1));
        let one = Q::one();
        let (pos, neg) = match a.op {
            DlOp::Le => (
                vec![Self::le(x, y, b_d.clone())],
                vec![if a.int_row {
                    Self::le(y, x, D::exact(b.neg().sub(&one)))
                } else {
                    Self::le(y, x, strict(&b.neg()))
                }],
            ),
            DlOp::Lt => (
                vec![Self::le(x, y, strict(b))],
                vec![Self::le(y, x, nb_d.clone())],
            ),
            DlOp::Ge => (
                vec![Self::le(y, x, nb_d.clone())],
                vec![if a.int_row {
                    Self::le(x, y, D::exact(b.sub(&one)))
                } else {
                    Self::le(x, y, strict(b))
                }],
            ),
            DlOp::Gt => (
                vec![Self::le(y, x, strict(&b.neg()))],
                vec![Self::le(x, y, b_d.clone())],
            ),
            DlOp::Eq => (
                vec![Self::le(x, y, b_d.clone()), Self::le(y, x, nb_d.clone())],
                vec![],
            ),
        };
        let idx = self.atoms.len();
        // single-edge atoms can be propagated in both polarities
        if pos.len() == 1 && neg.len() == 1 {
            self.alt_from[pos[0].0 as usize].push((idx, true));
            self.alt_from[neg[0].0 as usize].push((idx, false));
        }
        self.atom_of_var.insert(a.lit.abs(), idx);
        self.atoms.push(Atom {
            lit: a.lit,
            pos,
            neg,
        });
        self.truth.push(None);
    }

    /// Add the edge `from -> to` (weight `w`, justified by literal `lit`); `Err` is the
    /// clause of a negative cycle through it.
    fn add_edge(&mut self, from: u32, to: u32, w: D, lit: i32) -> Result<u32, Vec<i32>> {
        let id = self.edges.len() as u32;
        self.edges.push(Edge {
            from,
            to,
            w: w.clone(),
            lit,
        });
        self.out[from as usize].push(id);
        self.inn[to as usize].push(id);
        let need = self.pot[from as usize].add(&w);
        if self.pot[to as usize] <= need {
            return Ok(id);
        }
        // Repair the potentials with Dijkstra on reduced costs, starting at `to`.
        let mut gamma: HashMap<u32, D> = HashMap::new();
        let mut pred: HashMap<u32, u32> = HashMap::new();
        let mut moved: HashMap<u32, D> = HashMap::new();
        let mut heap: BinaryHeap<(Reverse<D>, u32)> = BinaryHeap::new();
        let g0 = need.sub(&self.pot[to as usize]);
        gamma.insert(to, g0.clone());
        pred.insert(to, id);
        heap.push((Reverse(g0), to));
        while let Some((Reverse(g), s)) = heap.pop() {
            if gamma.get(&s) != Some(&g) || moved.contains_key(&s) {
                continue; // stale
            }
            let new_pot_s = self.pot[s as usize].add(&g);
            moved.insert(s, new_pot_s.clone());
            let outs = self.out[s as usize].clone();
            for e2 in outs {
                let (t, w2) = (
                    self.edges[e2 as usize].to,
                    self.edges[e2 as usize].w.clone(),
                );
                if moved.contains_key(&t) {
                    continue;
                }
                let cand = new_pot_s.add(&w2).sub(&self.pot[t as usize]);
                if cand.c.signum() < 0 || (cand.c.is_zero() && cand.k.signum() < 0) {
                    if t == from {
                        // Negative cycle: e2 closes it; walk the predecessor chain back.
                        let mut cycle = vec![e2];
                        let mut cur = s;
                        loop {
                            let pe = pred[&cur];
                            cycle.push(pe);
                            cur = self.edges[pe as usize].from;
                            if pe == id {
                                break;
                            }
                        }
                        let mut clause: Vec<i32> =
                            cycle.iter().map(|&e| -self.edges[e as usize].lit).collect();
                        clause.sort_unstable();
                        clause.dedup();
                        self.conflicts += 1;
                        return Err(clause);
                    }
                    let better = match gamma.get(&t) {
                        None => true,
                        Some(cur) => cand < *cur,
                    };
                    if better {
                        gamma.insert(t, cand.clone());
                        pred.insert(t, e2);
                        heap.push((Reverse(cand), t));
                    }
                }
            }
        }
        for (n, p) in moved {
            self.pot[n as usize] = p;
        }
        Ok(id)
    }

    /// Nodes reachable from `src` through *tight* edges (reduced cost zero), forwards or
    /// backwards, with the edge that first reached each. Tight paths are shortest paths, and
    /// the search is a bounded breadth-first walk (Cotton & Maler's cheap propagation).
    fn tight_search(&self, src: u32, forward: bool) -> HashMap<u32, Option<u32>> {
        const NODE_LIMIT: usize = 48;
        const EDGE_SCAN: usize = 48;
        let mut reached: HashMap<u32, Option<u32>> = HashMap::new();
        reached.insert(src, None);
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(src);
        while let Some(s) = queue.pop_front() {
            if reached.len() >= NODE_LIMIT {
                break;
            }
            let adj = if forward {
                &self.out[s as usize]
            } else {
                &self.inn[s as usize]
            };
            for &e in adj.iter().rev().take(EDGE_SCAN) {
                let ed = &self.edges[e as usize];
                let t = if forward { ed.to } else { ed.from };
                if reached.contains_key(&t) {
                    continue;
                }
                let rc =
                    ed.w.add(&self.pot[ed.from as usize])
                        .sub(&self.pot[ed.to as usize]);
                if rc.c.is_zero() && rc.k.is_zero() {
                    reached.insert(t, Some(e));
                    queue.push_back(t);
                }
            }
        }
        reached
    }

    /// Edges of the tree path from the search source to `n`.
    fn tree_path(
        &self,
        tree: &HashMap<u32, Option<u32>>,
        n: u32,
        forward: bool,
        out: &mut Vec<u32>,
    ) {
        let mut cur = n;
        while let Some(Some(e)) = tree.get(&cur) {
            out.push(*e);
            let ed = &self.edges[*e as usize];
            cur = if forward { ed.from } else { ed.to };
        }
    }

    fn propagate_through(&mut self, eid: u32) {
        let e = self.edges[eid as usize].clone();
        let bwd = self.tight_search(e.from, false);
        if bwd.keys().all(|a| self.alt_from[*a as usize].is_empty()) {
            return;
        }
        let fwd = self.tight_search(e.to, true);
        // slack of the new edge itself: w + pot[from] - pot[to] >= 0
        let rc_e =
            e.w.add(&self.pot[e.from as usize])
                .sub(&self.pot[e.to as usize]);
        let backs: Vec<u32> = bwd.keys().copied().collect();
        for a in backs {
            if self.alt_from[a as usize].is_empty() {
                continue;
            }
            let cands: Vec<(usize, bool)> = self.alt_from[a as usize].clone();
            for (idx, polarity) in cands {
                if self.truth[idx].is_some() {
                    continue;
                }
                let (b, c, lit_implied) = {
                    let atom = &self.atoms[idx];
                    let v = if polarity { &atom.pos[0] } else { &atom.neg[0] };
                    (
                        v.1,
                        v.2.clone(),
                        if polarity { atom.lit } else { -atom.lit },
                    )
                };
                if !fwd.contains_key(&b) {
                    continue;
                }
                // path a ~> from -> to ~> b, all tight except possibly the new edge
                let total = rc_e.add(&self.pot[b as usize]).sub(&self.pot[a as usize]);
                if total <= c {
                    let mut path = Vec::new();
                    self.tree_path(&bwd, a, false, &mut path);
                    path.push(eid);
                    self.tree_path(&fwd, b, true, &mut path);
                    let mut clause: Vec<i32> =
                        path.iter().map(|&p| -self.edges[p as usize].lit).collect();
                    clause.push(lit_implied);
                    clause.sort_unstable();
                    clause.dedup();
                    self.pending.push((lit_implied, clause));
                }
            }
        }
    }
}

impl TheoryHook for DiffLogic {
    fn new_level(&mut self) {
        self.level_marks
            .push((self.asserted.len(), self.edges.len()));
    }

    fn backtrack(&mut self, level: usize) {
        while self.level_marks.len() > level {
            let (asserted_len, edges_len) = self.level_marks.pop().unwrap_or((0, 0));
            while self.asserted.len() > asserted_len {
                if let Some(idx) = self.asserted.pop() {
                    self.truth[idx] = None;
                }
            }
            while self.edges.len() > edges_len {
                if let Some(e) = self.edges.pop() {
                    self.out[e.from as usize].pop();
                    self.inn[e.to as usize].pop();
                }
            }
        }
        self.pending.clear();
    }

    fn assign(&mut self, lit: i32) -> Result<(), Vec<i32>> {
        if !self.enabled {
            return Ok(());
        }
        let Some(&idx) = self.atom_of_var.get(&lit.abs()) else {
            return Ok(());
        };
        let truth = lit > 0;
        self.truth[idx] = Some(truth);
        self.asserted.push(idx);
        let edges = if truth {
            self.atoms[idx].pos.clone()
        } else {
            self.atoms[idx].neg.clone()
        };
        let edge_lit = if truth {
            self.atoms[idx].lit
        } else {
            -self.atoms[idx].lit
        };
        let started = std::time::Instant::now();
        for (from, to, w) in edges {
            let t0 = std::time::Instant::now();
            let added = self.add_edge(from, to, w, edge_lit);
            self.repair_ns += t0.elapsed().as_nanos();
            let id = match added {
                Ok(id) => id,
                Err(c) => {
                    self.time_ns += started.elapsed().as_nanos();
                    return Err(c);
                }
            };
            if self.propagate {
                let t1 = std::time::Instant::now();
                self.propagate_through(id);
                self.search_ns += t1.elapsed().as_nanos();
            }
        }
        self.time_ns += started.elapsed().as_nanos();
        Ok(())
    }

    fn check(&mut self) -> Result<Vec<(i32, Vec<i32>)>, Vec<i32>> {
        let out = std::mem::take(&mut self.pending);
        self.propagations += out.len() as u64;
        Ok(out)
    }
}
