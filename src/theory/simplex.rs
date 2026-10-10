//! Incremental simplex for linear real arithmetic (Dutertre & de Moura, CAV 2006,
//! DOI 10.1007/11817963_11), with exact rationals and infinitesimals for strict bounds.
//!
//! The tableau persists across checks. Bounds are added and retracted through
//! [`Simplex::push`] / [`Simplex::pop`]; the assignment is kept, so each check starts from
//! the previous solution instead of from scratch. Reasons are opaque `u32` ids chosen by the
//! caller; a conflict is returned as the set of reasons whose bounds are jointly infeasible
//! (a Farkas certificate read off the violated row).
//!
//! Termination: Bland's rule (smallest violated basic variable, smallest suitable non-basic
//! variable) is used throughout, so cycling is impossible.

use super::qnum::{D, Q};
use std::collections::BTreeSet;

const NONE: u32 = u32::MAX;

#[derive(Clone, Debug)]
pub struct Bound {
    pub val: D,
    pub reason: u32,
}

#[derive(Clone, Debug)]
struct Row {
    basic: u32,
    /// Non-basic variables with coefficients, sorted by variable index.
    entries: Vec<(u32, Q)>,
}

enum Undo {
    Lower(u32, Option<Bound>),
    Upper(u32, Option<Bound>),
}

pub struct Simplex {
    lower: Vec<Option<Bound>>,
    upper: Vec<Option<Bound>>,
    value: Vec<D>,
    row_of: Vec<u32>,
    rows: Vec<Row>,
    /// Rows in which a variable occurs as non-basic. May hold stale or repeated entries;
    /// every use re-validates against the row and de-duplicates with `stamp`.
    cols: Vec<Vec<u32>>,
    is_int: Vec<bool>,
    trail: Vec<Undo>,
    marks: Vec<usize>,
    dirty: BTreeSet<u32>,
    stamp: Vec<u32>,
    epoch: u32,
    pub pivots: u64,
}

impl Default for Simplex {
    fn default() -> Self {
        Self::new()
    }
}

fn coeff(row: &Row, var: u32) -> Option<&Q> {
    row.entries
        .binary_search_by_key(&var, |(v, _)| *v)
        .ok()
        .map(|i| &row.entries[i].1)
}

/// `a + factor * b` for two sorted sparse vectors, dropping zeros. `added` receives the
/// variables of `b` that were not in `a`.
fn merge(a: &[(u32, Q)], b: &[(u32, Q)], factor: &Q, added: &mut Vec<u32>) -> Vec<(u32, Q)> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
            out.push(a[i].clone());
            i += 1;
        } else if i == a.len() || b[j].0 < a[i].0 {
            let c = b[j].1.mul(factor);
            if !c.is_zero() {
                added.push(b[j].0);
                out.push((b[j].0, c));
            }
            j += 1;
        } else {
            let c = a[i].1.add(&b[j].1.mul(factor));
            if !c.is_zero() {
                out.push((a[i].0, c));
            }
            i += 1;
            j += 1;
        }
    }
    out
}

impl Simplex {
    pub fn new() -> Self {
        Simplex {
            lower: Vec::new(),
            upper: Vec::new(),
            value: Vec::new(),
            row_of: Vec::new(),
            rows: Vec::new(),
            cols: Vec::new(),
            is_int: Vec::new(),
            trail: Vec::new(),
            marks: Vec::new(),
            dirty: BTreeSet::new(),
            stamp: Vec::new(),
            epoch: 0,
            pivots: 0,
        }
    }

    pub fn num_vars(&self) -> usize {
        self.value.len()
    }

    pub fn new_var(&mut self, is_int: bool) -> u32 {
        let id = self.value.len() as u32;
        self.lower.push(None);
        self.upper.push(None);
        self.value.push(D::zero());
        self.row_of.push(NONE);
        self.cols.push(Vec::new());
        self.is_int.push(is_int);
        id
    }

    pub fn is_int(&self, v: u32) -> bool {
        self.is_int[v as usize]
    }

    /// Current finite bounds of `v` (infinitesimal parts dropped: a strict bound is used as a
    /// non-strict one, which is weaker and therefore still valid).
    pub fn bounds(&self, v: u32) -> (Option<Q>, Option<Q>) {
        (
            self.lower[v as usize].as_ref().map(|b| b.val.c.clone()),
            self.upper[v as usize].as_ref().map(|b| b.val.c.clone()),
        )
    }

    pub fn value(&self, v: u32) -> &D {
        &self.value[v as usize]
    }

    /// Define a fresh variable `s = sum(coef * var)` and return it. Basic variables in
    /// `entries` are expanded through their rows so the new row only mentions non-basics.
    pub fn add_row(&mut self, entries: &[(u32, Q)]) -> u32 {
        let mut acc: std::collections::BTreeMap<u32, Q> = std::collections::BTreeMap::new();
        for (v, a) in entries {
            let r = self.row_of[*v as usize];
            if r == NONE {
                let e = acc.entry(*v).or_insert_with(Q::zero);
                *e = e.add(a);
            } else {
                for (w, b) in &self.rows[r as usize].entries {
                    let e = acc.entry(*w).or_insert_with(Q::zero);
                    *e = e.add(&a.mul(b));
                }
            }
        }
        let s = self.new_var(false);
        let ridx = self.rows.len() as u32;
        let list: Vec<(u32, Q)> = acc.into_iter().filter(|(_, c)| !c.is_zero()).collect();
        let mut val = D::zero();
        for (v, c) in &list {
            val = val.add(&self.value[*v as usize].scale(c));
            self.cols[*v as usize].push(ridx);
        }
        self.value[s as usize] = val;
        self.row_of[s as usize] = ridx;
        self.rows.push(Row {
            basic: s,
            entries: list,
        });
        self.stamp.push(0);
        s
    }

    pub fn push(&mut self) {
        self.marks.push(self.trail.len());
    }

    pub fn pop(&mut self) {
        let Some(mark) = self.marks.pop() else { return };
        while self.trail.len() > mark {
            match self.trail.pop() {
                Some(Undo::Lower(v, old)) => self.lower[v as usize] = old,
                Some(Undo::Upper(v, old)) => self.upper[v as usize] = old,
                None => break,
            }
        }
    }

    /// `v <= val`. Returns the conflicting reasons if this contradicts the lower bound.
    pub fn assert_upper(&mut self, v: u32, val: D, reason: u32) -> Result<(), Vec<u32>> {
        let i = v as usize;
        if self.upper[i].as_ref().is_some_and(|u| val >= u.val) {
            return Ok(());
        }
        if let Some(l) = &self.lower[i] {
            if val < l.val {
                return Err(vec![reason, l.reason]);
            }
        }
        let old = self.upper[i].replace(Bound {
            val: val.clone(),
            reason,
        });
        self.trail.push(Undo::Upper(v, old));
        if self.row_of[i] == NONE {
            if self.value[i] > val {
                self.update(v, val);
            }
        } else {
            self.dirty.insert(v);
        }
        Ok(())
    }

    /// `v >= val`. Returns the conflicting reasons if this contradicts the upper bound.
    pub fn assert_lower(&mut self, v: u32, val: D, reason: u32) -> Result<(), Vec<u32>> {
        let i = v as usize;
        if self.lower[i].as_ref().is_some_and(|l| val <= l.val) {
            return Ok(());
        }
        if let Some(u) = &self.upper[i] {
            if val > u.val {
                return Err(vec![reason, u.reason]);
            }
        }
        let old = self.lower[i].replace(Bound {
            val: val.clone(),
            reason,
        });
        self.trail.push(Undo::Lower(v, old));
        if self.row_of[i] == NONE {
            if self.value[i] < val {
                self.update(v, val);
            }
        } else {
            self.dirty.insert(v);
        }
        Ok(())
    }

    fn next_epoch(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.iter_mut().for_each(|s| *s = 0);
            self.epoch = 1;
        }
        self.epoch
    }

    /// Rows currently containing non-basic `x`, each once, with its coefficient.
    fn rows_of(&mut self, x: u32) -> Vec<(u32, Q)> {
        let epoch = self.next_epoch();
        let mut out = Vec::new();
        let list = std::mem::take(&mut self.cols[x as usize]);
        let mut kept = Vec::with_capacity(list.len());
        for r in list {
            if self.stamp[r as usize] == epoch {
                continue;
            }
            if let Some(c) = coeff(&self.rows[r as usize], x) {
                self.stamp[r as usize] = epoch;
                out.push((r, c.clone()));
                kept.push(r);
            }
        }
        self.cols[x as usize] = kept;
        out
    }

    /// Set non-basic `x` to `newval`, adjusting every basic variable that depends on it.
    fn update(&mut self, x: u32, newval: D) {
        let delta = newval.sub(&self.value[x as usize]);
        for (r, a) in self.rows_of(x) {
            let b = self.rows[r as usize].basic;
            self.value[b as usize] = self.value[b as usize].add(&delta.scale(&a));
            self.dirty.insert(b);
        }
        self.value[x as usize] = newval;
    }

    fn violated(&self, v: u32) -> Option<bool> {
        let i = v as usize;
        if let Some(l) = &self.lower[i] {
            if self.value[i] < l.val {
                return Some(true); // too low: must increase
            }
        }
        if let Some(u) = &self.upper[i] {
            if self.value[i] > u.val {
                return Some(false); // too high: must decrease
            }
        }
        None
    }

    /// Restore feasibility of all bounds, or return the reasons of an infeasible subset.
    pub fn check(&mut self) -> Result<(), Vec<u32>> {
        loop {
            let Some(&xi) = self.dirty.iter().next() else {
                return Ok(());
            };
            self.dirty.remove(&xi);
            if self.row_of[xi as usize] == NONE {
                continue;
            }
            let Some(increase) = self.violated(xi) else {
                continue;
            };
            let ridx = self.row_of[xi as usize] as usize;
            let mut chosen: Option<(u32, Q)> = None;
            for (xj, a) in &self.rows[ridx].entries {
                let j = *xj as usize;
                let pos = a.signum() > 0;
                // Can xj move in the direction that fixes xi?
                let ok = if increase == pos {
                    self.upper[j]
                        .as_ref()
                        .map_or(true, |u| self.value[j] < u.val)
                } else {
                    self.lower[j]
                        .as_ref()
                        .map_or(true, |l| self.value[j] > l.val)
                };
                if ok {
                    chosen = Some((*xj, a.clone()));
                    break;
                }
            }
            match chosen {
                None => {
                    self.dirty.insert(xi);
                    return Err(self.explain(xi, increase));
                }
                Some((xj, _)) => {
                    let target = if increase {
                        self.lower[xi as usize].as_ref().map(|b| b.val.clone())
                    } else {
                        self.upper[xi as usize].as_ref().map(|b| b.val.clone())
                    };
                    let Some(target) = target else { continue };
                    self.pivot_and_update(xi, xj, target);
                }
            }
        }
    }

    fn explain(&self, xi: u32, increase: bool) -> Vec<u32> {
        let mut out = Vec::new();
        let own = if increase {
            &self.lower[xi as usize]
        } else {
            &self.upper[xi as usize]
        };
        if let Some(b) = own {
            out.push(b.reason);
        }
        for (xj, a) in &self.rows[self.row_of[xi as usize] as usize].entries {
            let pos = a.signum() > 0;
            let blocking = if increase == pos {
                &self.upper[*xj as usize]
            } else {
                &self.lower[*xj as usize]
            };
            if let Some(b) = blocking {
                out.push(b.reason);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    fn pivot_and_update(&mut self, xi: u32, xj: u32, v: D) {
        self.pivots += 1;
        let ridx = self.row_of[xi as usize];
        let a = coeff(&self.rows[ridx as usize], xj)
            .cloned()
            .unwrap_or_else(Q::one);
        let theta = v.sub(&self.value[xi as usize]).div_q(&a);
        self.value[xi as usize] = v;
        self.value[xj as usize] = self.value[xj as usize].add(&theta);
        for (r, c) in self.rows_of(xj) {
            if r == ridx {
                continue;
            }
            let b = self.rows[r as usize].basic;
            self.value[b as usize] = self.value[b as usize].add(&theta.scale(&c));
            self.dirty.insert(b);
        }
        self.pivot(ridx, xi, xj);
        // The entering variable moved by theta and is now basic: it may lie outside its
        // own bounds, so it must be examined again.
        self.dirty.insert(xj);
    }

    fn pivot(&mut self, ridx: u32, xi: u32, xj: u32) {
        // Row ridx: xi = a*xj + sum(others)  ==>  xj = (1/a)*xi - sum(others)/a.
        let old = std::mem::take(&mut self.rows[ridx as usize].entries);
        let a = old
            .iter()
            .find(|(v, _)| *v == xj)
            .map(|(_, c)| c.clone())
            .unwrap_or_else(Q::one);
        let inv = Q::one().div(&a);
        let neg_inv = inv.neg();
        let mut new_entries: Vec<(u32, Q)> = Vec::with_capacity(old.len());
        for (v, c) in &old {
            if *v != xj {
                new_entries.push((*v, c.mul(&neg_inv)));
            }
        }
        new_entries.push((xi, inv));
        new_entries.sort_by_key(|(v, _)| *v);

        // The other rows containing xj, collected before xj turns basic.
        let others: Vec<(u32, Q)> = self
            .rows_of(xj)
            .into_iter()
            .filter(|(r, _)| *r != ridx)
            .collect();

        self.rows[ridx as usize] = Row {
            basic: xj,
            entries: new_entries.clone(),
        };
        self.row_of[xj as usize] = ridx;
        self.row_of[xi as usize] = NONE;
        self.cols[xi as usize].push(ridx);

        for (r, b) in others {
            let r_entries = std::mem::take(&mut self.rows[r as usize].entries);
            // Remove xj, then add b * (xj's definition).
            let without: Vec<(u32, Q)> = r_entries.into_iter().filter(|(v, _)| *v != xj).collect();
            let mut added = Vec::new();
            let merged = merge(&without, &new_entries, &b, &mut added);
            self.rows[r as usize].entries = merged;
            for v in added {
                self.cols[v as usize].push(r);
            }
        }
        self.cols[xj as usize].clear();
    }

    /// Check the tableau invariants: every basic value equals its row's linear combination
    /// and (after a successful `check`) every variable respects its bounds.
    pub fn validate(&self) -> Result<(), String> {
        for (ri, row) in self.rows.iter().enumerate() {
            let mut sum = D::zero();
            for (v, c) in &row.entries {
                if self.row_of[*v as usize] != NONE {
                    return Err(format!("row {ri}: entry {v} is basic"));
                }
                sum = sum.add(&self.value[*v as usize].scale(c));
            }
            if sum != self.value[row.basic as usize] {
                return Err(format!(
                    "row {ri}: basic {} has {:?} but its row sums to {:?}",
                    row.basic, self.value[row.basic as usize], sum
                ));
            }
            if self.row_of[row.basic as usize] != ri as u32 {
                return Err(format!(
                    "row {ri}: basic {} points to row {}",
                    row.basic, self.row_of[row.basic as usize]
                ));
            }
        }
        for i in 0..self.value.len() {
            if let Some(l) = &self.lower[i] {
                if self.value[i] < l.val {
                    return Err(format!(
                        "var {i} below lower bound {:?} (value {:?})",
                        l.val, self.value[i]
                    ));
                }
            }
            if let Some(u) = &self.upper[i] {
                if self.value[i] > u.val {
                    return Err(format!(
                        "var {i} above upper bound {:?} (value {:?})",
                        u.val, self.value[i]
                    ));
                }
            }
        }
        Ok(())
    }

    /// An integer variable whose current value is not an integer, with the integer
    /// `floor` such that the value lies in `(floor, floor + 1)` (infinitesimals included).
    pub fn fractional_int_var(&self) -> Option<(u32, Q)> {
        for (i, &is_int) in self.is_int.iter().enumerate() {
            if !is_int {
                continue;
            }
            let v = &self.value[i];
            if v.c.is_integer() && v.k.is_zero() {
                continue;
            }
            let floor = if v.c.is_integer() {
                if v.k.signum() < 0 {
                    v.c.sub(&Q::one())
                } else {
                    v.c.clone()
                }
            } else {
                v.c.floor()
            };
            return Some((i as u32, floor));
        }
        None
    }

    /// A concrete positive value for the infinitesimal that keeps every active bound
    /// satisfied by the current assignment.
    pub fn model_delta(&self) -> Q {
        let mut delta = Q::one();
        let mut tighten = |num: &Q, den: &Q| {
            // need delta <= num/den with den > 0, num > 0
            if num.signum() > 0 && den.signum() > 0 {
                let cand = num.div(den);
                if cand < delta {
                    delta = cand;
                }
            }
        };
        for i in 0..self.value.len() {
            let v = &self.value[i];
            if let Some(l) = &self.lower[i] {
                // l.c + l.k*d <= v.c + v.k*d
                if l.val.c < v.c && l.val.k > v.k {
                    tighten(&v.c.sub(&l.val.c), &l.val.k.sub(&v.k));
                }
            }
            if let Some(u) = &self.upper[i] {
                if v.c < u.val.c && v.k > u.val.k {
                    tighten(&u.val.c.sub(&v.c), &v.k.sub(&u.val.k));
                }
            }
        }
        // Stay strictly inside the tightest margin.
        delta.div(&Q::from_i64(2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Q {
        Q::from_i64(n)
    }

    #[test]
    fn detects_infeasible_difference_cycle() {
        // x - y <= 0, y - z <= 0, x - z >= 1  (infeasible)
        let mut s = Simplex::new();
        let (x, y, z) = (s.new_var(false), s.new_var(false), s.new_var(false));
        let a = s.add_row(&[(x, q(1)), (y, q(-1))]);
        let b = s.add_row(&[(y, q(1)), (z, q(-1))]);
        let c = s.add_row(&[(x, q(1)), (z, q(-1))]);
        s.push();
        s.assert_upper(a, D::exact(q(0)), 1).unwrap();
        s.assert_upper(b, D::exact(q(0)), 2).unwrap();
        s.assert_lower(c, D::exact(q(1)), 3).unwrap();
        let conflict = s.check().unwrap_err();
        assert_eq!(conflict, vec![1, 2, 3]);
        s.pop();
        // The same tableau is reusable after retracting the bounds.
        s.push();
        s.assert_upper(a, D::exact(q(0)), 1).unwrap();
        s.assert_upper(b, D::exact(q(0)), 2).unwrap();
        s.assert_lower(c, D::exact(q(-5)), 3).unwrap();
        assert!(s.check().is_ok());
    }

    fn frac(n: i64, d: i64) -> Q {
        q(n).div(&q(d))
    }

    #[test]
    fn variables_and_bounds_are_reported() {
        let mut s = Simplex::new();
        assert_eq!(s.num_vars(), 0);
        let x = s.new_var(false);
        let n = s.new_var(true);
        assert_eq!(s.num_vars(), 2);
        assert!(!s.is_int(x) && s.is_int(n));
        assert_eq!(s.bounds(x), (None, None));
        s.assert_lower(x, D::exact(q(2)), 1).unwrap();
        s.assert_upper(x, D::exact(q(7)), 2).unwrap();
        assert_eq!(s.bounds(x), (Some(q(2)), Some(q(7))));
        assert_eq!(s.bounds(n), (None, None));
    }

    #[test]
    fn equal_bounds_are_consistent_and_crossing_bounds_conflict_with_both_reasons() {
        let mut s = Simplex::new();
        let x = s.new_var(false);
        s.assert_lower(x, D::exact(q(5)), 1).unwrap();
        s.assert_upper(x, D::exact(q(5)), 2).unwrap(); // x = 5 is allowed
        assert!(s.check().is_ok());
        assert_eq!(s.value(x), &D::exact(q(5)));
        let mut s = Simplex::new();
        let y = s.new_var(false);
        s.assert_lower(y, D::exact(q(5)), 1).unwrap();
        assert_eq!(s.assert_upper(y, D::exact(q(4)), 2), Err(vec![2, 1]));
        let mut s = Simplex::new();
        let z = s.new_var(false);
        s.assert_upper(z, D::exact(q(4)), 1).unwrap();
        assert_eq!(s.assert_lower(z, D::exact(q(5)), 2), Err(vec![2, 1]));
        // a weaker bound than the current one changes nothing
        let mut s = Simplex::new();
        let w = s.new_var(false);
        s.assert_upper(w, D::exact(q(3)), 1).unwrap();
        s.assert_upper(w, D::exact(q(9)), 2).unwrap();
        assert_eq!(s.bounds(w).1, Some(q(3)));
        s.assert_lower(w, D::exact(q(-3)), 3).unwrap();
        s.assert_lower(w, D::exact(q(-9)), 4).unwrap();
        assert_eq!(s.bounds(w).0, Some(q(-3)));
    }

    #[test]
    fn fractional_integer_variable_reports_its_floor() {
        let mut s = Simplex::new();
        let r = s.new_var(false);
        let n = s.new_var(true);
        assert_eq!(s.fractional_int_var(), None);
        // a real variable with a fractional value is not reported
        s.assert_lower(r, D::exact(frac(1, 2)), 1).unwrap();
        assert_eq!(s.fractional_int_var(), None);
        // an integer variable at 5/2 has floor 2, at -5/2 floor -3
        s.assert_lower(n, D::exact(frac(5, 2)), 2).unwrap();
        assert_eq!(s.fractional_int_var(), Some((n, q(2))));
        let mut t = Simplex::new();
        let m = t.new_var(true);
        t.assert_upper(m, D::exact(frac(-5, 2)), 1).unwrap();
        assert_eq!(t.fractional_int_var(), Some((m, q(-3))));
        // integer centre with an infinitesimal: 3 - d lies in (2, 3), 3 + d in (3, 4)
        let mut u = Simplex::new();
        let a = u.new_var(true);
        u.assert_lower(a, D::new(q(3), q(-1)), 1).unwrap();
        assert_eq!(u.fractional_int_var(), Some((a, q(2))));
        let mut v = Simplex::new();
        let b = v.new_var(true);
        v.assert_lower(b, D::new(q(3), q(1)), 1).unwrap();
        assert_eq!(v.fractional_int_var(), Some((b, q(3))));
        // an exact integer is not reported
        let mut w = Simplex::new();
        let c = w.new_var(true);
        w.assert_lower(c, D::exact(q(4)), 1).unwrap();
        assert_eq!(w.fractional_int_var(), None);
    }

    #[test]
    fn model_delta_stays_inside_the_tightest_margin() {
        // lower 4 + 3d, value 6: need 4 + 3d <= 6, so d <= 2/3; the result is half of it
        let mut s = Simplex::new();
        let x = s.new_var(false);
        s.value[x as usize] = D::exact(q(6));
        s.lower[x as usize] = Some(Bound {
            val: D::new(q(4), q(3)),
            reason: 1,
        });
        assert_eq!(s.model_delta(), frac(1, 3));
        // upper 4 + 1d, value 1 + 5d: need 1 + 5d <= 4 + d, so d <= 3/4
        let mut t = Simplex::new();
        let y = t.new_var(false);
        t.value[y as usize] = D::new(q(1), q(5));
        t.upper[y as usize] = Some(Bound {
            val: D::new(q(4), q(1)),
            reason: 1,
        });
        assert_eq!(t.model_delta(), frac(3, 8));
        // the smaller of two margins wins, and the cap is 1/2
        let mut u = Simplex::new();
        let a = u.new_var(false);
        let b = u.new_var(false);
        u.value[a as usize] = D::exact(q(6));
        u.lower[a as usize] = Some(Bound {
            val: D::new(q(4), q(3)),
            reason: 1,
        });
        u.value[b as usize] = D::new(q(1), q(5));
        u.upper[b as usize] = Some(Bound {
            val: D::new(q(4), q(1)),
            reason: 2,
        });
        assert_eq!(u.model_delta(), frac(1, 3));
        assert_eq!(Simplex::new().model_delta(), frac(1, 2));
        // bounds that already hold with the infinitesimal part ignored do not constrain d
        let mut w = Simplex::new();
        let c = w.new_var(false);
        w.value[c as usize] = D::exact(q(6));
        w.lower[c as usize] = Some(Bound {
            val: D::new(q(4), q(-3)),
            reason: 1,
        });
        assert_eq!(w.model_delta(), frac(1, 2));
    }

    #[test]
    fn validate_accepts_a_feasible_tableau_and_names_each_kind_of_corruption() {
        let build = || {
            let mut s = Simplex::new();
            let (x, y) = (s.new_var(false), s.new_var(false));
            let r = s.add_row(&[(x, q(1)), (y, q(1))]);
            s.assert_lower(x, D::exact(q(1)), 1).unwrap();
            s.assert_lower(y, D::exact(q(2)), 2).unwrap();
            s.assert_upper(r, D::exact(q(10)), 3).unwrap();
            assert!(s.check().is_ok());
            (s, x, r)
        };
        let (s, _, _) = build();
        assert_eq!(s.validate(), Ok(()));
        // basic value no longer equals its row
        let (mut bad, _, r) = build();
        bad.value[r as usize] = D::exact(q(99));
        assert!(bad.validate().unwrap_err().contains("row sums"));
        // value below a lower bound (the row is kept consistent so only the bound is wrong)
        let (mut bad, x, r) = build();
        bad.value[x as usize] = D::exact(q(0));
        bad.value[r as usize] = D::exact(q(2));
        assert!(bad.validate().unwrap_err().contains("below lower bound"));
        // value above an upper bound
        let (mut bad, x, r) = build();
        bad.value[x as usize] = D::exact(q(20));
        bad.value[r as usize] = D::exact(q(22));
        assert!(bad.validate().unwrap_err().contains("above upper bound"));
        // basic pointer mismatch
        let (mut bad, _, r) = build();
        bad.row_of[r as usize] = 7;
        assert!(bad.validate().is_err());
    }

    #[test]
    fn explanation_of_a_lower_violation_names_the_blocking_upper_bounds() {
        // r = x + y with r >= 10, x <= 3, y <= 4: infeasible, reasons are the three bounds
        let mut s = Simplex::new();
        let (x, y) = (s.new_var(false), s.new_var(false));
        let r = s.add_row(&[(x, q(1)), (y, q(1))]);
        s.assert_upper(x, D::exact(q(3)), 11).unwrap();
        s.assert_upper(y, D::exact(q(4)), 12).unwrap();
        s.assert_lower(r, D::exact(q(10)), 13).unwrap();
        assert_eq!(s.check(), Err(vec![11, 12, 13]));
        // an upper violation: r <= 1 with x >= 3, y >= 4
        let mut t = Simplex::new();
        let (x, y) = (t.new_var(false), t.new_var(false));
        let r = t.add_row(&[(x, q(1)), (y, q(1))]);
        t.assert_lower(x, D::exact(q(3)), 21).unwrap();
        t.assert_lower(y, D::exact(q(4)), 22).unwrap();
        t.assert_upper(r, D::exact(q(1)), 23).unwrap();
        assert_eq!(t.check(), Err(vec![21, 22, 23]));
        // a negative coefficient flips which bound blocks
        let mut u = Simplex::new();
        let (x, y) = (u.new_var(false), u.new_var(false));
        let r = u.add_row(&[(x, q(1)), (y, q(-1))]);
        u.assert_upper(x, D::exact(q(0)), 31).unwrap();
        u.assert_upper(y, D::exact(q(5)), 32).unwrap(); // y can still grow: no blocking
        u.assert_lower(y, D::exact(q(5)), 33).unwrap();
        u.assert_lower(r, D::exact(q(1)), 34).unwrap(); // x - y >= 1 needs x >= 6 > 0
        assert_eq!(u.check(), Err(vec![31, 33, 34]));
    }

    #[test]
    fn strict_bounds_use_the_infinitesimal() {
        let mut s = Simplex::new();
        let x = s.new_var(false);
        s.push();
        s.assert_lower(x, D::new(q(0), q(1)), 1).unwrap(); // x > 0
        s.assert_upper(x, D::new(q(1), q(-1)), 2).unwrap(); // x < 1
        assert!(s.check().is_ok());
        let d = s.model_delta();
        let v = s.value(x).c.add(&s.value(x).k.mul(&d));
        assert!(v > q(0) && v < q(1));
        s.pop();
        s.push();
        s.assert_lower(x, D::new(q(1), q(1)), 1).unwrap(); // x > 1
        assert!(s.assert_upper(x, D::new(q(1), q(-1)), 2).is_err());
    }
}
