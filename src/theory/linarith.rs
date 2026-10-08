//! Linear arithmetic over the rationals and integers on top of the persistent
//! [`Simplex`].
//!
//! Atoms are registered once, when the SAT literal is created: the comparison is turned
//! into a canonical polynomial, mapped to a (shared) simplex row, and stored as a bound
//! `row op constant`. Each DPLL(T) iteration then only asserts the bounds implied by the
//! current SAT assignment on the persistent tableau, which is warm-started from the
//! previous solution.
//!
//! Integer rows (all variables `Int`) are scaled to coprime integer coefficients and their
//! bounds rounded, so strict integer inequalities never reach the simplex. Integrality of
//! the final solution is enforced by the caller through branch-and-bound lemmas.

use super::diff::{DlAtom, DlOp};
use super::qnum::{D, Q};
use super::simplex::Simplex;
use crate::ast::{Expr, Type};
use crate::sat::TheoryHook;
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use std::collections::{BTreeMap, HashMap};

const NO_VAR: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

impl Op {
    fn flip(self) -> Op {
        match self {
            Op::Le => Op::Ge,
            Op::Lt => Op::Gt,
            Op::Ge => Op::Le,
            Op::Gt => Op::Lt,
            Op::Eq => Op::Eq,
        }
    }
}

#[derive(Clone, Debug)]
struct Atom {
    lit: i32,
    /// Simplex variable carrying the polynomial, or `NO_VAR` for a constant comparison.
    var: u32,
    op: Op,
    bound: Q,
    int_row: bool,
}

/// A product `x * y` of two variables, abstracted to the variable `name`.
#[derive(Clone, Debug)]
pub struct Monomial {
    pub name: String,
    pub x: Expr,
    pub y: Expr,
}

pub struct LinArith {
    sx: Simplex,
    var_ids: HashMap<String, u32>,
    var_names: HashMap<u32, String>,
    abstraction: HashMap<String, u32>,
    rows: HashMap<Vec<(u32, String)>, u32>,
    atoms: Vec<Atom>,
    /// SAT variable -> index of the atom it stands for.
    atom_of_var: HashMap<i32, usize>,
    /// Atoms per simplex variable (for bound propagation between atoms on one row).
    var_atoms: HashMap<u32, Vec<usize>>,
    /// Current truth of each atom, as announced by the SAT core.
    truth: Vec<Option<bool>>,
    /// Atoms asserted so far, in order, and where each decision level starts.
    asserted: Vec<usize>,
    level_marks: Vec<usize>,
    pending: Vec<(i32, Vec<i32>)>,
    pub conflicts: u64,
    pub propagations: u64,
    pub time_ns: u128,
    /// A term no linear rule covers was abstracted to a fresh variable: sound for unsat,
    /// but a satisfiable verdict is not trustworthy while this is set.
    pub abstracted: bool,
    /// A product of non-constants was abstracted (the NLA theory must decide it).
    pub nonlinear: bool,
    last_dl: Option<DlAtom>,
    monomials: Vec<Monomial>,
    monomial_ids: HashMap<(String, String), String>,
}

impl Default for LinArith {
    fn default() -> Self {
        Self::new()
    }
}

fn gcd(a: BigInt, b: BigInt) -> BigInt {
    let (mut a, mut b) = (a.abs(), b.abs());
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a
}

/// Positive factor turning the coefficients into coprime integers.
fn integer_scale(coeffs: &[(u32, Q)]) -> Option<Q> {
    let mut lcm = BigInt::from(1);
    for (_, c) in coeffs {
        let (_, d) = c.parts();
        lcm = &lcm / gcd(lcm.clone(), d.clone()) * d;
    }
    let mut g = BigInt::from(0);
    for (_, c) in coeffs {
        let (n, d) = c.parts();
        g = gcd(g, n * &lcm / d);
    }
    if g.is_zero() {
        None
    } else {
        Some(Q::from_big(&num_rational::BigRational::new(lcm, g)))
    }
}

impl LinArith {
    pub fn new() -> Self {
        LinArith {
            sx: Simplex::new(),
            var_ids: HashMap::new(),
            var_names: HashMap::new(),
            abstraction: HashMap::new(),
            rows: HashMap::new(),
            atoms: Vec::new(),
            atom_of_var: HashMap::new(),
            var_atoms: HashMap::new(),
            truth: Vec::new(),
            asserted: Vec::new(),
            level_marks: Vec::new(),
            pending: Vec::new(),
            conflicts: 0,
            propagations: 0,
            time_ns: 0,
            abstracted: false,
            nonlinear: false,
            last_dl: None,
            monomials: Vec::new(),
            monomial_ids: HashMap::new(),
        }
    }

    /// Current bounds of a named variable under the asserted atoms.
    pub fn var_bounds(&self, name: &str) -> (Option<Q>, Option<Q>) {
        match self.var_ids.get(name) {
            Some(&id) => self.sx.bounds(id),
            None => (None, None),
        }
    }

    pub fn monomials(&self) -> &[Monomial] {
        &self.monomials
    }

    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    pub fn pivots(&self) -> u64 {
        self.sx.pivots
    }

    fn user_var(&mut self, name: &str, is_int: bool) -> u32 {
        if let Some(&id) = self.var_ids.get(name) {
            return id;
        }
        let id = self.sx.new_var(is_int);
        self.var_ids.insert(name.to_string(), id);
        self.var_names.insert(id, name.to_string());
        id
    }

    fn abstract_var(&mut self, key: String) -> u32 {
        if let Some(&id) = self.abstraction.get(&key) {
            return id;
        }
        let id = self.sx.new_var(false);
        self.abstraction.insert(key, id);
        id
    }

    fn constant(e: &Expr) -> Option<Q> {
        match e {
            Expr::Int(_) | Expr::Real(_, _) | Expr::BigRat(_, _) => {
                e.as_rational().map(|r| Q::from_big(&r))
            }
            Expr::Add(v) => v
                .iter()
                .try_fold(Q::zero(), |a, x| Some(a.add(&Self::constant(x)?))),
            Expr::Mul(v) => v
                .iter()
                .try_fold(Q::one(), |a, x| Some(a.mul(&Self::constant(x)?))),
            Expr::Sub(v) => match v.as_slice() {
                [] => Some(Q::zero()),
                [only] => Some(Self::constant(only)?.neg()),
                [first, rest @ ..] => rest.iter().try_fold(Self::constant(first)?, |a, x| {
                    Some(a.sub(&Self::constant(x)?))
                }),
            },
            Expr::Div(a, b) => {
                let d = Self::constant(b)?;
                if d.is_zero() {
                    None
                } else {
                    Some(Self::constant(a)?.div(&d))
                }
            }
            _ => None,
        }
    }

    fn extract(&mut self, e: &Expr, scale: &Q, acc: &mut BTreeMap<u32, Q>, cst: &mut Q) {
        match e {
            Expr::Int(_) | Expr::Real(_, _) | Expr::BigRat(_, _) => {
                if let Some(c) = Self::constant(e) {
                    *cst = cst.add(&scale.mul(&c));
                }
            }
            Expr::Var(name, ty @ (Type::Int | Type::Real)) => {
                let id = self.user_var(name, *ty == Type::Int);
                let slot = acc.entry(id).or_insert_with(Q::zero);
                *slot = slot.add(scale);
            }
            Expr::Add(args) => {
                for a in args {
                    self.extract(a, scale, acc, cst);
                }
            }
            Expr::Sub(args) => match args.as_slice() {
                [] => {}
                [only] => self.extract(only, &scale.neg(), acc, cst),
                [first, rest @ ..] => {
                    self.extract(first, scale, acc, cst);
                    for a in rest {
                        self.extract(a, &scale.neg(), acc, cst);
                    }
                }
            },
            Expr::Mul(args) => {
                let mut factor = Q::one();
                let mut rest: Vec<&Expr> = Vec::new();
                for a in args {
                    match Self::constant(a) {
                        Some(c) => factor = factor.mul(&c),
                        None => rest.push(a),
                    }
                }
                match rest.as_slice() {
                    [] => *cst = cst.add(&scale.mul(&factor)),
                    [only] => self.extract(only, &scale.mul(&factor), acc, cst),
                    [Expr::Var(xn, xt), Expr::Var(yn, yt)] if rest.len() == 2 => {
                        // A plain product of two variables: a named monomial the solver
                        // refines with lemmas (incremental linearization).
                        let key = if xn <= yn {
                            (xn.clone(), yn.clone())
                        } else {
                            (yn.clone(), xn.clone())
                        };
                        let both_int = *xt == Type::Int && *yt == Type::Int;
                        let name = match self.monomial_ids.get(&key) {
                            Some(n) => n.clone(),
                            None => {
                                let n = format!("__mul_{}", self.monomials.len());
                                self.monomial_ids.insert(key, n.clone());
                                self.monomials.push(Monomial {
                                    name: n.clone(),
                                    x: Expr::Var(xn.clone(), xt.clone()),
                                    y: Expr::Var(yn.clone(), yt.clone()),
                                });
                                n
                            }
                        };
                        let id = self.user_var(&name, both_int);
                        let slot = acc.entry(id).or_insert_with(Q::zero);
                        *slot = slot.add(&scale.mul(&factor));
                    }
                    _ => {
                        self.nonlinear = true;
                        let id = self.abstract_var(format!("{e:?}"));
                        let slot = acc.entry(id).or_insert_with(Q::zero);
                        *slot = slot.add(scale);
                    }
                }
            }
            Expr::Div(a, b) => match Self::constant(b) {
                Some(d) if !d.is_zero() => self.extract(a, &scale.div(&d), acc, cst),
                _ => {
                    self.abstracted = true;
                    let id = self.abstract_var(format!("{e:?}"));
                    let slot = acc.entry(id).or_insert_with(Q::zero);
                    *slot = slot.add(scale);
                }
            },
            other => {
                self.abstracted = true;
                let id = self.abstract_var(format!("{other:?}"));
                let slot = acc.entry(id).or_insert_with(Q::zero);
                *slot = slot.add(scale);
            }
        }
    }

    /// Register the arithmetic atom `expr` (a comparison) under SAT literal `lit`.
    /// Returns false if `expr` is not a comparison this theory handles.
    pub fn register(&mut self, lit: i32, expr: &Expr) -> bool {
        let (a, b, op) = match expr {
            Expr::Le(a, b) => (a, b, Op::Le),
            Expr::Lt(a, b) => (a, b, Op::Lt),
            Expr::Ge(a, b) => (a, b, Op::Ge),
            Expr::Gt(a, b) => (a, b, Op::Gt),
            Expr::Eq(a, b) => (a, b, Op::Eq),
            _ => return false,
        };
        let mut acc: BTreeMap<u32, Q> = BTreeMap::new();
        let mut cst = Q::zero();
        self.extract(a, &Q::one(), &mut acc, &mut cst);
        self.extract(b, &Q::one().neg(), &mut acc, &mut cst);
        let mut poly: Vec<(u32, Q)> = acc.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        // poly + cst  op  0   ==>   poly  op  -cst
        let mut bound = cst.neg();
        let mut op = op;

        self.last_dl = None;
        if poly.is_empty() {
            self.push_atom(Atom {
                lit,
                var: NO_VAR,
                op,
                bound,
                int_row: false,
            });
            return true;
        }

        let int_row = poly.iter().all(|(v, _)| self.sx.is_int(*v));
        // Scale: coprime integers for integer rows, leading coefficient 1 for real rows.
        let scale = if int_row {
            integer_scale(&poly).unwrap_or_else(Q::one)
        } else {
            Q::one().div(&poly[0].1.abs())
        };
        for (_, c) in poly.iter_mut() {
            *c = c.mul(&scale);
        }
        bound = bound.mul(&scale);
        if poly[0].1.signum() < 0 {
            for (_, c) in poly.iter_mut() {
                *c = c.neg();
            }
            bound = bound.neg();
            op = op.flip();
        }

        let key: Vec<(u32, String)> = poly.iter().map(|(v, c)| (*v, c.to_string())).collect();
        let var = if poly.len() == 1 && poly[0].1 == Q::one() {
            poly[0].0
        } else if let Some(&row) = self.rows.get(&key) {
            row
        } else {
            let row = self.sx.add_row(&poly);
            self.rows.insert(key, row);
            row
        };

        if int_row {
            // x < b  ==  x <= ceil(b) - 1 ;  x > b  ==  x >= floor(b) + 1
            match op {
                Op::Le => bound = bound.floor(),
                Op::Lt => {
                    bound = bound.ceil().sub(&Q::one());
                    op = Op::Le;
                }
                Op::Ge => bound = bound.ceil(),
                Op::Gt => {
                    bound = bound.floor().add(&Q::one());
                    op = Op::Ge;
                }
                Op::Eq => {}
            }
        }
        // Difference-logic shape (`u - v op c` or `u op c`) for the accelerator.
        let shape = match poly.as_slice() {
            [(u, c)] if *c == Q::one() => Some((*u, None)),
            [(u, c1), (v, c2)] if *c1 == Q::one() && *c2 == Q::from_i64(-1) => Some((*u, Some(*v))),
            _ => None,
        };
        self.last_dl = shape.map(|(u, v)| DlAtom {
            lit,
            u,
            v,
            op: match op {
                Op::Le => DlOp::Le,
                Op::Lt => DlOp::Lt,
                Op::Ge => DlOp::Ge,
                Op::Gt => DlOp::Gt,
                Op::Eq => DlOp::Eq,
            },
            bound: bound.clone(),
            int_row,
        });
        self.push_atom(Atom {
            lit,
            var,
            op,
            bound,
            int_row,
        });
        true
    }

    /// The difference-logic form of the atom registered last, if it has one.
    pub fn take_dl(&mut self) -> Option<DlAtom> {
        self.last_dl.take()
    }

    fn push_atom(&mut self, atom: Atom) {
        let idx = self.atoms.len();
        self.atom_of_var.insert(atom.lit.abs(), idx);
        if atom.var != NO_VAR {
            self.var_atoms.entry(atom.var).or_default().push(idx);
        }
        self.atoms.push(atom);
        self.truth.push(None);
    }

    pub fn atom_lit(&self, idx: usize) -> i32 {
        self.atoms[idx].lit
    }

    /// Bounds on the atom's simplex variable implied by the atom being `truth`.
    fn bounds_of(&self, idx: usize, truth: bool) -> (Option<D>, Option<D>) {
        let atom = &self.atoms[idx];
        let b = &atom.bound;
        if truth {
            match atom.op {
                Op::Le => (None, Some(D::exact(b.clone()))),
                Op::Lt => (None, Some(D::new(b.clone(), Q::from_i64(-1)))),
                Op::Ge => (Some(D::exact(b.clone())), None),
                Op::Gt => (Some(D::new(b.clone(), Q::one())), None),
                Op::Eq => {
                    if atom.int_row && !b.is_integer() {
                        // No integer point on this row: contradictory bounds.
                        (Some(D::exact(b.ceil())), Some(D::exact(b.floor())))
                    } else {
                        (Some(D::exact(b.clone())), Some(D::exact(b.clone())))
                    }
                }
            }
        } else {
            match atom.op {
                Op::Le if atom.int_row => (Some(D::exact(b.add(&Q::one()))), None),
                Op::Le => (Some(D::new(b.clone(), Q::one())), None),
                Op::Lt => (Some(D::exact(b.clone())), None),
                Op::Ge if atom.int_row => (None, Some(D::exact(b.sub(&Q::one())))),
                Op::Ge => (None, Some(D::new(b.clone(), Q::from_i64(-1)))),
                Op::Gt => (None, Some(D::exact(b.clone()))),
                Op::Eq => (None, None),
            }
        }
    }

    fn assert_atom(&mut self, idx: usize, truth: bool) -> Result<(), Vec<u32>> {
        let atom = self.atoms[idx].clone();
        let reason = idx as u32;
        if atom.var == NO_VAR {
            // 0 op bound
            let ord = Q::zero().cmp(&atom.bound);
            let holds = match atom.op {
                Op::Le => ord.is_le(),
                Op::Lt => ord.is_lt(),
                Op::Ge => ord.is_ge(),
                Op::Gt => ord.is_gt(),
                Op::Eq => ord.is_eq(),
            };
            return if holds == truth {
                Ok(())
            } else {
                Err(vec![reason])
            };
        }
        let (lower, upper) = self.bounds_of(idx, truth);
        if let Some(u) = upper {
            self.sx.assert_upper(atom.var, u, reason)?;
        }
        if let Some(l) = lower {
            self.sx.assert_lower(atom.var, l, reason)?;
        }
        Ok(())
    }

    /// The clause forbidding the atoms in `reasons` from all holding as currently assigned.
    fn conflict_clause(&self, reasons: &[u32]) -> Vec<i32> {
        let mut clause: Vec<i32> = reasons
            .iter()
            .filter_map(|&r| {
                let idx = r as usize;
                self.truth[idx].map(|t| {
                    if t {
                        -self.atoms[idx].lit
                    } else {
                        self.atoms[idx].lit
                    }
                })
            })
            .collect();
        clause.sort_unstable();
        clause.dedup();
        clause
    }

    /// After asserting `idx`, queue the atoms on the same row that it decides.
    fn propagate_from(&mut self, idx: usize, truth: bool) {
        const SCAN_LIMIT: usize = 256;
        let var = self.atoms[idx].var;
        if var == NO_VAR {
            return;
        }
        let (new_low, new_up) = self.bounds_of(idx, truth);
        if new_low.is_none() && new_up.is_none() {
            return;
        }
        let premise = if truth {
            self.atoms[idx].lit
        } else {
            -self.atoms[idx].lit
        };
        let Some(others) = self.var_atoms.get(&var).cloned() else {
            return;
        };
        for &b in others.iter().take(SCAN_LIMIT) {
            if b == idx || self.truth[b].is_some() {
                continue;
            }
            let (b_low, b_up) = self.bounds_of(b, true);
            // New region contained in b's region: b holds.
            let lower_ok = match (&b_low, &new_low) {
                (None, _) => true,
                (Some(bl), Some(nl)) => nl >= bl,
                (Some(_), None) => false,
            };
            let upper_ok = match (&b_up, &new_up) {
                (None, _) => true,
                (Some(bu), Some(nu)) => nu <= bu,
                (Some(_), None) => false,
            };
            let disjoint = matches!((&new_up, &b_low), (Some(nu), Some(bl)) if nu < bl)
                || matches!((&new_low, &b_up), (Some(nl), Some(bu)) if nl > bu);
            let blit = self.atoms[b].lit;
            if lower_ok && upper_ok {
                self.pending.push((blit, vec![blit, -premise]));
            } else if disjoint {
                self.pending.push((-blit, vec![-blit, -premise]));
            }
        }
    }

    /// An integer variable (by name) whose value is fractional, and its floor.
    pub fn fractional_int(&self) -> Option<(String, Q)> {
        let (v, floor) = self.sx.fractional_int_var()?;
        self.var_names.get(&v).map(|n| (n.clone(), floor))
    }

    /// Concrete model value of every named variable (call before `release`).
    pub fn assignments(&self) -> Vec<(String, num_rational::BigRational)> {
        let delta = self.sx.model_delta();
        let mut out: Vec<_> = self
            .var_names
            .iter()
            .map(|(&id, name)| {
                let v = self.sx.value(id);
                (name.clone(), v.c.add(&v.k.mul(&delta)).to_big())
            })
            .collect();
        out.sort();
        out
    }
}

impl TheoryHook for LinArith {
    fn new_level(&mut self) {
        self.sx.push();
        self.level_marks.push(self.asserted.len());
    }

    fn backtrack(&mut self, level: usize) {
        while self.level_marks.len() > level {
            self.sx.pop();
            let mark = self.level_marks.pop().unwrap_or(0);
            while self.asserted.len() > mark {
                if let Some(idx) = self.asserted.pop() {
                    self.truth[idx] = None;
                }
            }
        }
        self.pending.clear();
    }

    fn assign(&mut self, lit: i32) -> Result<(), Vec<i32>> {
        let Some(&idx) = self.atom_of_var.get(&lit.abs()) else {
            return Ok(());
        };
        let started = std::time::Instant::now();
        let truth = lit > 0;
        self.truth[idx] = Some(truth);
        self.asserted.push(idx);
        let result = match self.assert_atom(idx, truth) {
            Ok(()) => {
                self.propagate_from(idx, truth);
                Ok(())
            }
            Err(reasons) => {
                self.conflicts += 1;
                Err(self.conflict_clause(&reasons))
            }
        };
        self.time_ns += started.elapsed().as_nanos();
        result
    }

    fn check(&mut self) -> Result<Vec<(i32, Vec<i32>)>, Vec<i32>> {
        let started = std::time::Instant::now();
        let outcome = match self.sx.check() {
            Ok(()) => {
                let out = std::mem::take(&mut self.pending);
                self.propagations += out.len() as u64;
                Ok(out)
            }
            Err(reasons) => {
                self.conflicts += 1;
                self.pending.clear();
                Err(self.conflict_clause(&reasons))
            }
        };
        self.time_ns += started.elapsed().as_nanos();
        if outcome.is_ok() && std::env::var_os("RZ3_VALIDATE").is_some() {
            if let Err(msg) = self.sx.validate() {
                eprintln!("SIMPLEX INVARIANT BROKEN: {msg}");
            }
        }
        outcome
    }
}
