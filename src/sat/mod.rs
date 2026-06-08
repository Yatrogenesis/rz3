use std::collections::{BinaryHeap, BTreeMap};
use std::cmp::Ordering;

pub type Literal = i32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClauseIdx(pub usize);

#[derive(Debug, Clone, Copy)]
struct Watch {
    blocker: Literal,
    idx: ClauseIdx,
}

pub struct ClauseArena {
    data: Vec<i32>,
    /// Mapeo de ID -> (Actividad, LBD)
    metadata: BTreeMap<usize, (f32, usize)>,
}

impl ClauseArena {
    fn new() -> Self {
        Self { 
            data: Vec::with_capacity(1024),
            metadata: BTreeMap::new(),
        }
    }

    fn push(&mut self, lits: &[Literal], learned: bool, lbd: usize) -> ClauseIdx {
        let idx = self.data.len();
        // Header: (longitud << 2) | (borrada << 1) | (aprendida)
        let header = ((lits.len() as i32) << 2) | (if learned { 1 } else { 0 });
        self.data.push(header);
        self.data.extend_from_slice(lits);
        if learned {
            self.metadata.insert(idx, (0.0, lbd));
        }
        ClauseIdx(idx)
    }

    #[inline] fn is_deleted(&self, idx: ClauseIdx) -> bool { (self.data[idx.0] & 2) != 0 }
    #[inline] fn mark_deleted(&mut self, idx: ClauseIdx) { self.data[idx.0] |= 2; }
    #[inline] fn bump_activity(&mut self, idx: ClauseIdx, inc: f32) {
        if let Some(meta) = self.metadata.get_mut(&idx.0) { meta.0 += inc; }
    }
    #[inline] fn get_len(&self, idx: ClauseIdx) -> usize { (self.data[idx.0] >> 2) as usize }
    #[inline] fn get_lits_mut(&mut self, idx: ClauseIdx) -> &mut [Literal] {
        let len = self.get_len(idx);
        &mut self.data[idx.0 + 1..idx.0 + 1 + len]
    }
    #[inline] fn get_lit(&self, idx: ClauseIdx, i: usize) -> Literal { self.data[idx.0 + 1 + i] }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assignment { True, False, Unassigned }

#[derive(Debug, Clone, Copy, PartialEq)]
struct Activity { score: f64, var: usize }
impl Eq for Activity {}
impl Ord for Activity {
    // Determinismo explícito: en empate de score, desempatar por índice de variable
    // (orden total), sin depender de la estructura interna del heap. [Fase 3]
    fn cmp(&self, other: &Self) -> Ordering {
        self.score
            .partial_cmp(&other.score)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.var.cmp(&other.var))
    }
}
impl PartialOrd for Activity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

pub struct CdclSolver {
    clauses: ClauseArena,
    watches: Vec<Vec<Watch>>,
    assignments: Vec<Assignment>,
    levels: Vec<usize>,
    reasons: Vec<Option<ClauseIdx>>,
    trail: Vec<Literal>,
    trail_lim: Vec<usize>,
    qhead: usize,
    current_level: usize,
    scores: Vec<f64>,
    phases: Vec<Assignment>,
    activity_heap: BinaryHeap<Activity>,
    score_inc: f64,
    pub ok: bool,
}

impl Default for CdclSolver { fn default() -> Self { Self::new() } }

impl CdclSolver {
    pub fn new() -> Self {
        Self {
            clauses: ClauseArena::new(),
            watches: Vec::new(),
            assignments: Vec::new(),
            levels: Vec::new(),
            reasons: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            current_level: 0,
            scores: Vec::new(),
            phases: Vec::new(),
            activity_heap: BinaryHeap::new(),
            score_inc: 1.0,
            ok: true,
        }
    }

    fn ensure_var(&mut self, var: usize) {
        if var >= self.assignments.len() {
            let old_len = self.assignments.len();
            self.assignments.resize(var + 1, Assignment::Unassigned);
            self.levels.resize(var + 1, 0);
            self.reasons.resize(var + 1, None);
            self.scores.resize(var + 1, 0.0);
            self.phases.resize(var + 1, Assignment::False);
            self.watches.resize((var + 1) * 2 + 2, Vec::new());
            for i in old_len..=var { self.activity_heap.push(Activity { score: 0.0, var: i }); }
        }
    }

    fn lit_to_idx(&self, lit: Literal) -> usize {
        if lit > 0 { (lit as usize) * 2 } else { (lit.unsigned_abs() as usize) * 2 + 1 }
    }

    pub fn add_clause(&mut self, mut lits: Vec<Literal>) -> Option<ClauseIdx> {
        if !self.ok { return None; }
        if lits.is_empty() { self.ok = false; return None; }
        for &lit in &lits { self.ensure_var(lit.unsigned_abs() as usize); }
        lits.sort_unstable(); lits.dedup();
        for i in 0..lits.len().saturating_sub(1) { if lits[i] == -lits[i+1] { return None; } }
        let mut i = 0;
        while i < lits.len() {
            let val = self.get_lit_value(lits[i]);
            let level = self.levels[lits[i].unsigned_abs() as usize];
            if val == Assignment::True && level == 0 { return None; }
            if val == Assignment::False && level == 0 { lits.swap_remove(i); continue; }
            i += 1;
        }
        if lits.is_empty() { self.ok = false; return None; }
        if lits.len() == 1 { self.assign(lits[0], 0, None); return None; }

        let learned = self.current_level > 0;
        let lbd = if learned { self.calculate_lbd(&lits) } else { 0 };
        let clause_idx = self.clauses.push(&lits, learned, lbd);
        
        let lit0 = self.clauses.get_lit(clause_idx, 0);
        let lit1 = self.clauses.get_lit(clause_idx, 1);
        let idx0 = self.lit_to_idx(-lit0);
        let idx1 = self.lit_to_idx(-lit1);
        self.watches[idx0].push(Watch { blocker: lit1, idx: clause_idx });
        self.watches[idx1].push(Watch { blocker: lit0, idx: clause_idx });
        Some(clause_idx)
    }

    fn calculate_lbd(&self, lits: &[Literal]) -> usize {
        let mut lvls = Vec::new();
        for &l in lits {
            let lvl = self.levels[l.unsigned_abs() as usize];
            if !lvls.contains(&lvl) { lvls.push(lvl); }
        }
        lvls.len()
    }

    fn assign(&mut self, lit: Literal, level: usize, reason: Option<ClauseIdx>) {
        if !self.ok { return; }
        let var = lit.unsigned_abs() as usize;
        let val = if lit > 0 { Assignment::True } else { Assignment::False };
        if self.assignments[var] == Assignment::Unassigned {
            self.assignments[var] = val; self.levels[var] = level;
            self.reasons[var] = reason; self.trail.push(lit);
        } else if self.assignments[var] != val { self.ok = false; }
    }

    pub fn unit_propagate(&mut self) -> Result<(), ClauseIdx> {
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead]; self.qhead += 1;
            let lit_idx = self.lit_to_idx(lit);
            let mut i = 0;
            while i < self.watches[lit_idx].len() {
                let watch = self.watches[lit_idx][i];
                if self.get_lit_value(watch.blocker) == Assignment::True { i += 1; continue; }
                if self.clauses.is_deleted(watch.idx) { self.watches[lit_idx].swap_remove(i); continue; }
                if self.clauses.get_lit(watch.idx, 0) == -lit { self.clauses.get_lits_mut(watch.idx).swap(0, 1); }
                let first_lit = self.clauses.get_lit(watch.idx, 0);
                if self.get_lit_value(first_lit) == Assignment::True { self.watches[lit_idx][i].blocker = first_lit; i += 1; continue; }
                let mut found = false;
                let len = self.clauses.get_len(watch.idx);
                for j in 2..len {
                    let cand = self.clauses.get_lit(watch.idx, j);
                    if self.get_lit_value(cand) != Assignment::False {
                        self.clauses.get_lits_mut(watch.idx).swap(1, j);
                        let idx = self.lit_to_idx(-cand);
                        self.watches[idx].push(Watch { blocker: first_lit, idx: watch.idx });
                        self.watches[lit_idx].swap_remove(i);
                        found = true; break;
                    }
                }
                if !found {
                    if self.get_lit_value(first_lit) == Assignment::False { return Err(watch.idx); }
                    else if self.get_lit_value(first_lit) == Assignment::Unassigned { self.assign(first_lit, self.current_level, Some(watch.idx)); }
                    i += 1;
                }
            }
        }
        Ok(())
    }

    pub fn solve(&mut self) -> bool {
        if !self.ok { return false; }
        let mut conflict_count = 0;

        if self.unit_propagate().is_err() { self.ok = false; return false; }
        loop {
            if let Err(conflict_idx) = self.unit_propagate() {
                conflict_count += 1;
                if self.current_level == 0 { self.ok = false; return false; }
                if conflict_count % 1000 == 0 { self.reduce_learned(); }
                let (learnt_lits, backtrack_level) = self.analyze_conflict(conflict_idx);
                self.decay_scores();
                self.backtrack(backtrack_level);
                if let Some(learnt_idx) = self.add_clause(learnt_lits) {
                    if let Some(unit_lit) = self.check_unit_clause(learnt_idx) { self.assign(unit_lit, self.current_level, Some(learnt_idx)); }
                }
                continue;
            }
            if let Some(var) = self.pick_branching_variable() {
                self.current_level += 1; self.trail_lim.push(self.trail.len());
                let lit = if self.phases[var] == Assignment::True { var as i32 } else { -(var as i32) };
                self.assign(lit, self.current_level, None);
            } else { return true; }
        }
    }

    fn check_unit_clause(&self, idx: ClauseIdx) -> Option<Literal> {
        let mut unassigned = None;
        for i in 0..self.clauses.get_len(idx) {
            let lit = self.clauses.get_lit(idx, i);
            match self.get_lit_value(lit) {
                Assignment::True => return None,
                Assignment::Unassigned => { if unassigned.is_some() { return None; } unassigned = Some(lit); }
                Assignment::False => {}
            }
        }
        unassigned
    }

    pub fn get_lit_value(&self, lit: Literal) -> Assignment {
        let var = lit.unsigned_abs() as usize;
        let assign = self.assignments[var];
        if assign == Assignment::Unassigned { return Assignment::Unassigned; }
        if lit > 0 { assign } else { match assign { Assignment::True => Assignment::False, Assignment::False => Assignment::True, _ => unreachable!() } }
    }

    fn reduce_learned(&mut self) {
        let mut learned = self.clauses.metadata.iter().map(|(&idx, &(act, lbd))| (idx, act, lbd)).collect::<Vec<_>>();
        learned.sort_by(|a, b| a.2.cmp(&b.2).then(a.1.partial_cmp(&b.1).unwrap_or(Ordering::Equal)));
        for (idx_val, _, lbd) in learned.iter().take(learned.len() / 2) {
            let idx = ClauseIdx(*idx_val);
            if *lbd <= 2 { continue; } // Keep high-quality clauses
            let var = self.clauses.get_lit(idx, 0).unsigned_abs() as usize;
            if self.reasons[var] != Some(idx) { self.clauses.mark_deleted(idx); self.clauses.metadata.remove(idx_val); }
        }
    }

    fn pick_branching_variable(&mut self) -> Option<usize> {
        while let Some(Activity { score: _, var }) = self.activity_heap.pop() {
            if self.assignments[var] == Assignment::Unassigned { return Some(var); }
        }
        None
    }

    fn decay_scores(&mut self) { self.score_inc /= 0.95; }
    fn bump_score(&mut self, var: usize) {
        self.scores[var] += self.score_inc; self.activity_heap.push(Activity { score: self.scores[var], var });
        if self.scores[var] > 1e100 {
            for (i, s) in self.scores.iter_mut().enumerate() { *s *= 1e-100; self.activity_heap.push(Activity { score: *s, var: i }); }
            self.score_inc *= 1e-100;
        }
    }

    fn backtrack(&mut self, level: usize) {
        while self.current_level > level {
            let start = self.trail_lim.pop().unwrap();
            for i in start..self.trail.len() {
                let var = self.trail[i].unsigned_abs() as usize;
                self.phases[var] = self.assignments[var];
                self.assignments[var] = Assignment::Unassigned; self.reasons[var] = None; self.levels[var] = 0;
            }
            self.trail.truncate(start); self.current_level -= 1;
        }
        self.qhead = self.trail.len();
    }

    fn analyze_conflict(&mut self, conflict_idx: ClauseIdx) -> (Vec<Literal>, usize) {
        let mut learnt_lits = Vec::new();
        let mut seen = vec![false; self.assignments.len()];
        let mut counter = 0; let mut p = self.trail.len() as isize - 1;
        let mut current = conflict_idx;
        loop {
            self.clauses.bump_activity(current, 1.0);
            for i in 0..self.clauses.get_len(current) {
                let var = self.clauses.get_lit(current, i).unsigned_abs() as usize;
                if !seen[var] && self.levels[var] > 0 {
                    seen[var] = true; self.bump_score(var);
                    if self.levels[var] >= self.current_level { counter += 1; }
                    else { learnt_lits.push(self.clauses.get_lit(current, i)); }
                }
            }
            while p >= 0 && !seen[self.trail[p as usize].unsigned_abs() as usize] { p -= 1; }
            if counter <= 1 || p < 0 { break; }
            let last_var = self.trail[p as usize].unsigned_abs() as usize;
            seen[last_var] = false; counter -= 1;
            if let Some(reason) = self.reasons[last_var] { current = reason; } else { break; }
            p -= 1;
        }
        if p >= 0 { learnt_lits.push(-self.trail[p as usize]); }
        let backtrack_level = learnt_lits.iter().map(|&l| self.levels[l.unsigned_abs() as usize]).filter(|&lvl| lvl < self.current_level).max().unwrap_or(0);
        (learnt_lits, backtrack_level)
    }
}
