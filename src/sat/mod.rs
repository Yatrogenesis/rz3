use std::cmp::Ordering;
use std::collections::{BTreeMap, BinaryHeap};

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
    metadata: BTreeMap<usize, (u64, usize)>,
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
            self.metadata.insert(idx, (0, lbd));
        }
        ClauseIdx(idx)
    }

    #[inline]
    fn is_deleted(&self, idx: ClauseIdx) -> bool {
        (self.data[idx.0] & 2) != 0
    }
    #[inline]
    fn mark_deleted(&mut self, idx: ClauseIdx) {
        self.data[idx.0] |= 2;
    }
    #[inline]
    fn bump_activity(&mut self, idx: ClauseIdx, inc: u64) {
        if let Some(meta) = self.metadata.get_mut(&idx.0) {
            meta.0 = meta.0.saturating_add(inc);
        }
    }
    #[inline]
    fn get_len(&self, idx: ClauseIdx) -> usize {
        (self.data[idx.0] >> 2) as usize
    }
    #[inline]
    fn get_lits_mut(&mut self, idx: ClauseIdx) -> &mut [Literal] {
        let len = self.get_len(idx);
        &mut self.data[idx.0 + 1..idx.0 + 1 + len]
    }
    #[inline]
    fn get_lit(&self, idx: ClauseIdx, i: usize) -> Literal {
        self.data[idx.0 + 1 + i]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assignment {
    True,
    False,
    Unassigned,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Activity {
    score: u64,
    var: usize,
}
impl Ord for Activity {
    // Determinismo explícito: en empate de score, desempatar por índice de variable
    // (orden total), sin depender de la estructura interna del heap. [Fase 3]
    fn cmp(&self, other: &Self) -> Ordering {
        self.score
            .cmp(&other.score)
            .then_with(|| self.var.cmp(&other.var))
    }
}
impl PartialOrd for Activity {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Callbacks that let a theory take part in the search (DPLL(T)).
///
/// The SAT core owns the trail. It announces every decision level it opens
/// ([`TheoryHook::new_level`]) and every level it abandons ([`TheoryHook::backtrack`]),
/// forwards each literal that becomes true ([`TheoryHook::assign`]) and, at every
/// propagation fixpoint, asks the theory whether the assignment is still consistent
/// ([`TheoryHook::check`]). A conflict is a clause whose literals are all currently false.
pub trait TheoryHook {
    fn new_level(&mut self);
    /// Forget everything asserted above decision level `level`.
    fn backtrack(&mut self, level: usize);
    fn assign(&mut self, lit: Literal) -> Result<(), Vec<Literal>>;
    /// Theory consequences: `(implied literal, reason clause)` where the reason clause
    /// contains the implied literal and is otherwise false. Or a conflict clause.
    #[allow(clippy::type_complexity)]
    fn check(&mut self) -> Result<Vec<(Literal, Vec<Literal>)>, Vec<Literal>>;
}

/// The trivial theory: pure SAT.
pub struct NoTheory;

impl TheoryHook for NoTheory {
    fn new_level(&mut self) {}
    fn backtrack(&mut self, _level: usize) {}
    fn assign(&mut self, _lit: Literal) -> Result<(), Vec<Literal>> {
        Ok(())
    }
    fn check(&mut self) -> Result<Vec<(Literal, Vec<Literal>)>, Vec<Literal>> {
        Ok(Vec::new())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveStatus {
    Sat,
    Unsat,
    /// Stopped by the deadline; the instance is undecided.
    Interrupted,
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
    scores: Vec<u64>,
    phases: Vec<Assignment>,
    activity_heap: BinaryHeap<Activity>,
    score_inc: u64,
    /// Scratch marks for conflict analysis (kept allocated; cleared after each use).
    seen: Vec<bool>,
    /// Trail literals below this index have been announced to the theory.
    th_head: usize,
    /// The solver was unwound outside `solve_with`, so the theory must be re-synchronised.
    hook_dirty: bool,
    restarts: u64,
    pub ok: bool,
}

impl Default for CdclSolver {
    fn default() -> Self {
        Self::new()
    }
}

fn luby(mut i: u64) -> u64 {
    // 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
    let mut size = 1u64;
    let mut seq = 0u32;
    while size < i + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != i {
        size = (size - 1) >> 1;
        seq -= 1;
        i %= size;
    }
    1u64 << seq
}

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
            score_inc: 1,
            seen: Vec::new(),
            th_head: 0,
            hook_dirty: false,
            restarts: 0,
            ok: true,
        }
    }

    fn ensure_var(&mut self, var: usize) {
        if var >= self.assignments.len() {
            let old_len = self.assignments.len();
            self.assignments.resize(var + 1, Assignment::Unassigned);
            self.levels.resize(var + 1, 0);
            self.reasons.resize(var + 1, None);
            self.scores.resize(var + 1, 0);
            self.phases.resize(var + 1, Assignment::False);
            self.seen.resize(var + 1, false);
            self.watches.resize((var + 1) * 2 + 2, Vec::new());
            for i in old_len..=var {
                self.activity_heap.push(Activity { score: 0, var: i });
            }
        }
    }

    fn lit_to_idx(&self, lit: Literal) -> usize {
        if lit > 0 {
            (lit as usize) * 2
        } else {
            (lit.unsigned_abs() as usize) * 2 + 1
        }
    }

    /// Add a problem clause. The solver is first unwound to decision level 0: after a
    /// successful `solve()` it still holds a full assignment at deeper levels, and adding
    /// a clause (or a unit) on top of that left watches on already-false literals and
    /// let units contradict stale assignments, which produced spurious unsat/sat.
    pub fn add_clause(&mut self, lits: Vec<Literal>) -> Option<ClauseIdx> {
        if self.current_level > 0 {
            self.hook_dirty = true;
        }
        self.backtrack(0);
        self.add_clause_inner(lits)
    }

    fn add_clause_inner(&mut self, mut lits: Vec<Literal>) -> Option<ClauseIdx> {
        if !self.ok {
            return None;
        }
        if lits.is_empty() {
            self.ok = false;
            return None;
        }
        for &lit in &lits {
            self.ensure_var(lit.unsigned_abs() as usize);
        }
        lits.sort_unstable();
        lits.dedup();
        for i in 0..lits.len().saturating_sub(1) {
            if lits[i] == -lits[i + 1] {
                return None;
            }
        }
        let mut i = 0;
        while i < lits.len() {
            let val = self.get_lit_value(lits[i]);
            let level = self.levels[lits[i].unsigned_abs() as usize];
            if val == Assignment::True && level == 0 {
                return None;
            }
            if val == Assignment::False && level == 0 {
                lits.swap_remove(i);
                continue;
            }
            i += 1;
        }
        if lits.is_empty() {
            self.ok = false;
            return None;
        }
        if lits.len() == 1 {
            self.assign(lits[0], 0, None);
            return None;
        }
        let clause_idx = self.clauses.push(&lits, false, 0);
        self.watch_clause(clause_idx);
        Some(clause_idx)
    }

    fn watch_clause(&mut self, clause_idx: ClauseIdx) {
        let lit0 = self.clauses.get_lit(clause_idx, 0);
        let lit1 = self.clauses.get_lit(clause_idx, 1);
        let idx0 = self.lit_to_idx(-lit0);
        let idx1 = self.lit_to_idx(-lit1);
        self.watches[idx0].push(Watch {
            blocker: lit1,
            idx: clause_idx,
        });
        self.watches[idx1].push(Watch {
            blocker: lit0,
            idx: clause_idx,
        });
    }

    fn calculate_lbd(&self, lits: &[Literal]) -> usize {
        let mut lvls: Vec<usize> = lits
            .iter()
            .map(|&l| self.levels[l.unsigned_abs() as usize])
            .collect();
        lvls.sort_unstable();
        lvls.dedup();
        lvls.len()
    }

    fn assign(&mut self, lit: Literal, level: usize, reason: Option<ClauseIdx>) {
        if !self.ok {
            return;
        }
        let var = lit.unsigned_abs() as usize;
        let val = if lit > 0 {
            Assignment::True
        } else {
            Assignment::False
        };
        if self.assignments[var] == Assignment::Unassigned {
            self.assignments[var] = val;
            self.levels[var] = level;
            self.reasons[var] = reason;
            self.trail.push(lit);
        } else if self.assignments[var] != val {
            self.ok = false;
        }
    }

    pub fn unit_propagate(&mut self) -> Result<(), ClauseIdx> {
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            let lit_idx = self.lit_to_idx(lit);
            let mut i = 0;
            while i < self.watches[lit_idx].len() {
                let watch = self.watches[lit_idx][i];
                if self.get_lit_value(watch.blocker) == Assignment::True {
                    i += 1;
                    continue;
                }
                if self.clauses.is_deleted(watch.idx) {
                    self.watches[lit_idx].swap_remove(i);
                    continue;
                }
                if self.clauses.get_lit(watch.idx, 0) == -lit {
                    self.clauses.get_lits_mut(watch.idx).swap(0, 1);
                }
                let first_lit = self.clauses.get_lit(watch.idx, 0);
                if self.get_lit_value(first_lit) == Assignment::True {
                    self.watches[lit_idx][i].blocker = first_lit;
                    i += 1;
                    continue;
                }
                let mut found = false;
                let len = self.clauses.get_len(watch.idx);
                for j in 2..len {
                    let cand = self.clauses.get_lit(watch.idx, j);
                    if self.get_lit_value(cand) != Assignment::False {
                        self.clauses.get_lits_mut(watch.idx).swap(1, j);
                        let idx = self.lit_to_idx(-cand);
                        self.watches[idx].push(Watch {
                            blocker: first_lit,
                            idx: watch.idx,
                        });
                        self.watches[lit_idx].swap_remove(i);
                        found = true;
                        break;
                    }
                }
                if !found {
                    if self.get_lit_value(first_lit) == Assignment::False {
                        return Err(watch.idx);
                    } else if self.get_lit_value(first_lit) == Assignment::Unassigned {
                        self.assign(first_lit, self.current_level, Some(watch.idx));
                    }
                    i += 1;
                }
            }
        }
        Ok(())
    }

    /// Pure SAT solving (no theory).
    pub fn solve(&mut self) -> bool {
        self.solve_with(&mut NoTheory, None) == SolveStatus::Sat
    }

    /// CDCL search with a theory consulted at every propagation fixpoint.
    pub fn solve_with(
        &mut self,
        th: &mut dyn TheoryHook,
        deadline: Option<std::time::Instant>,
    ) -> SolveStatus {
        if !self.ok {
            return SolveStatus::Unsat;
        }
        if self.hook_dirty {
            th.backtrack(0);
            self.hook_dirty = false;
        }
        self.backtrack_with(0, th);

        let mut conflicts_this_restart = 0u64;
        let mut restart_limit = 100 * luby(self.restarts);
        let mut conflicts_total = 0u64;
        loop {
            if !self.ok {
                return SolveStatus::Unsat;
            }
            // 1. Boolean propagation, then the theory, until nothing new happens.
            let mut conflict: Option<ConflictSource> = match self.unit_propagate() {
                Err(idx) => Some(ConflictSource::Clause(idx)),
                Ok(()) => None,
            };
            if conflict.is_none() {
                conflict = self.sync_theory(th);
                if conflict.is_none() && self.qhead < self.trail.len() {
                    continue; // theory propagations to process
                }
            }
            if let Some(c) = conflict {
                conflicts_total += 1;
                conflicts_this_restart += 1;
                if let Some(d) = deadline {
                    if conflicts_total % 64 == 0 && std::time::Instant::now() > d {
                        return SolveStatus::Interrupted;
                    }
                }
                if !self.resolve_conflict(c, th) {
                    return SolveStatus::Unsat;
                }
                if conflicts_total % 2000 == 0 {
                    self.reduce_learned();
                }
                continue;
            }
            // 2. Restart?
            if conflicts_this_restart >= restart_limit {
                self.restarts += 1;
                restart_limit = 100 * luby(self.restarts);
                conflicts_this_restart = 0;
                self.backtrack_with(0, th);
                continue;
            }
            // 3. Decide.
            match self.pick_branching_variable() {
                Some(var) => {
                    self.current_level += 1;
                    self.trail_lim.push(self.trail.len());
                    th.new_level();
                    let lit = if self.phases[var] == Assignment::True {
                        var as i32
                    } else {
                        -(var as i32)
                    };
                    self.assign(lit, self.current_level, None);
                }
                None => {
                    if let Some(d) = deadline {
                        if std::time::Instant::now() > d {
                            return SolveStatus::Interrupted;
                        }
                    }
                    return SolveStatus::Sat;
                }
            }
        }
    }

    /// Announce new trail literals to the theory and run its consistency check.
    fn sync_theory(&mut self, th: &mut dyn TheoryHook) -> Option<ConflictSource> {
        let mut announced = false;
        while self.th_head < self.trail.len() {
            let lit = self.trail[self.th_head];
            self.th_head += 1;
            announced = true;
            if let Err(clause) = th.assign(lit) {
                return Some(ConflictSource::Lits(clause));
            }
        }
        if !announced {
            return None;
        }
        match th.check() {
            Err(clause) => Some(ConflictSource::Lits(clause)),
            Ok(implied) => {
                for (lit, reason) in implied {
                    match self.get_lit_value(lit) {
                        Assignment::True => {}
                        Assignment::False => {
                            // The reason clause is falsified: a conflict.
                            return Some(ConflictSource::Lits(reason));
                        }
                        Assignment::Unassigned => {
                            let mut clause = reason;
                            // implied literal first, as the analysis expects of reasons
                            if let Some(pos) = clause.iter().position(|&l| l == lit) {
                                clause.swap(0, pos);
                            }
                            if clause.len() >= 2 {
                                let lbd = self.calculate_lbd(&clause);
                                let idx = self.clauses.push(&clause, true, lbd);
                                // Not watched: it only serves as the reason of this propagation.
                                self.assign(lit, self.current_level, Some(idx));
                            } else {
                                self.assign(lit, self.current_level, None);
                            }
                        }
                    }
                }
                None
            }
        }
    }

    /// Learn from a conflict and backjump. `false` means the instance is unsatisfiable.
    fn resolve_conflict(&mut self, source: ConflictSource, th: &mut dyn TheoryHook) -> bool {
        let confl = match source {
            ConflictSource::Clause(idx) => idx,
            ConflictSource::Lits(mut lits) => {
                lits.sort_unstable();
                lits.dedup();
                for &l in &lits {
                    self.ensure_var(l.unsigned_abs() as usize);
                }
                if lits
                    .iter()
                    .any(|&l| self.get_lit_value(l) != Assignment::False)
                {
                    // The theory reported a clause that is not falsified: ignore it
                    // rather than corrupt the search (it would signal a theory bug).
                    return self.ok;
                }
                let level_of = |s: &Self, l: Literal| s.levels[l.unsigned_abs() as usize];
                let max_level = lits.iter().map(|&l| level_of(self, l)).max().unwrap_or(0);
                if lits.is_empty() || max_level == 0 {
                    self.ok = false;
                    return false;
                }
                if max_level < self.current_level {
                    self.backtrack_with(max_level, th);
                }
                // Order: highest-level literals first (the watch scheme needs two of them).
                lits.sort_by_key(|&l| std::cmp::Reverse(level_of(self, l)));
                let at_max = lits
                    .iter()
                    .filter(|&&l| level_of(self, l) == max_level)
                    .count();
                let lbd = self.calculate_lbd(&lits);
                if lits.len() == 1 {
                    self.backtrack_with(0, th);
                    self.assign(lits[0], 0, None);
                    return self.ok;
                }
                let idx = self.clauses.push(&lits, true, lbd);
                self.watch_clause(idx);
                if at_max == 1 {
                    // Asserting after backjumping to the second-highest level.
                    let second = level_of(self, lits[1]);
                    self.backtrack_with(second, th);
                    let asserting = lits[0];
                    self.assign(asserting, self.current_level, Some(idx));
                    return self.ok;
                }
                idx
            }
        };
        if self.current_level == 0 {
            self.ok = false;
            return false;
        }
        let (learnt, backtrack_level) = self.analyze(confl);
        self.decay_scores();
        self.backtrack_with(backtrack_level, th);
        if learnt.len() == 1 {
            self.assign(learnt[0], 0, None);
        } else {
            let lbd = self.calculate_lbd(&learnt);
            let idx = self.clauses.push(&learnt, true, lbd);
            self.watch_clause(idx);
            self.assign(learnt[0], self.current_level, Some(idx));
        }
        self.ok
    }

    pub fn get_lit_value(&self, lit: Literal) -> Assignment {
        let var = lit.unsigned_abs() as usize;
        let assign = self.assignments[var];
        if assign == Assignment::Unassigned {
            return Assignment::Unassigned;
        }
        if lit > 0 {
            assign
        } else {
            match assign {
                Assignment::True => Assignment::False,
                Assignment::False => Assignment::True,
                _ => unreachable!(),
            }
        }
    }

    fn reduce_learned(&mut self) {
        let mut learned = self
            .clauses
            .metadata
            .iter()
            .map(|(&idx, &(act, lbd))| (idx, act, lbd))
            .collect::<Vec<_>>();
        learned.sort_by(|a, b| a.2.cmp(&b.2).then(a.1.cmp(&b.1)));
        let keep_from = learned.len() / 2;
        for (idx_val, _, lbd) in learned.iter().skip(keep_from) {
            let idx = ClauseIdx(*idx_val);
            if *lbd <= 2 || self.clauses.is_deleted(idx) {
                continue; // keep high-quality clauses
            }
            // A clause that is currently the reason of an assignment must stay.
            let locked = (0..self.clauses.get_len(idx)).any(|i| {
                let var = self.clauses.get_lit(idx, i).unsigned_abs() as usize;
                self.reasons[var] == Some(idx)
            });
            if !locked {
                self.clauses.mark_deleted(idx);
                self.clauses.metadata.remove(idx_val);
            }
        }
    }

    fn pick_branching_variable(&mut self) -> Option<usize> {
        while let Some(Activity { score: _, var }) = self.activity_heap.pop() {
            if var != 0 && self.assignments[var] == Assignment::Unassigned {
                return Some(var);
            }
        }
        None
    }

    fn decay_scores(&mut self) {
        self.score_inc = self.score_inc.saturating_mul(105).saturating_add(99) / 100;
        self.score_inc = self.score_inc.max(1);
    }

    fn bump_score(&mut self, var: usize) {
        self.scores[var] = self.scores[var].saturating_add(self.score_inc);
        self.activity_heap.push(Activity {
            score: self.scores[var],
            var,
        });
        if self.scores[var] > 1_000_000_000_000_000_000 {
            for (i, s) in self.scores.iter_mut().enumerate() {
                *s /= 1_000_000;
                self.activity_heap.push(Activity { score: *s, var: i });
            }
            self.score_inc = (self.score_inc / 1_000_000).max(1);
        }
    }

    /// Unwind the trail to `level` and tell the theory.
    fn backtrack_with(&mut self, level: usize, th: &mut dyn TheoryHook) {
        if self.current_level > level {
            self.backtrack(level);
            th.backtrack(level);
        }
    }

    fn backtrack(&mut self, level: usize) {
        while self.current_level > level {
            let start = self.trail_lim.pop().unwrap();
            for i in start..self.trail.len() {
                let var = self.trail[i].unsigned_abs() as usize;
                self.phases[var] = self.assignments[var];
                self.assignments[var] = Assignment::Unassigned;
                self.reasons[var] = None;
                self.levels[var] = 0;
                // `pick_branching_variable` discards assigned variables from the heap;
                // an unassigned one must be selectable again or `solve` would stop with
                // free variables and report a satisfying assignment that is not one.
                self.activity_heap.push(Activity {
                    score: self.scores[var],
                    var,
                });
            }
            self.trail.truncate(start);
            self.current_level -= 1;
        }
        // Literals still on the trail below the target level were fully propagated, but
        // units appended at level 0 since the last propagation may not have been.
        self.qhead = self.qhead.min(self.trail.len());
        self.th_head = self.th_head.min(self.trail.len());
    }

    /// 1-UIP conflict analysis with local clause minimisation. Returns the learnt clause
    /// (asserting literal first, highest remaining level second) and the backjump level.
    fn analyze(&mut self, conflict_idx: ClauseIdx) -> (Vec<Literal>, usize) {
        let mut learnt: Vec<Literal> = vec![0];
        let mut touched: Vec<usize> = Vec::new();
        let mut path = 0usize;
        let mut index = self.trail.len();
        let mut current = conflict_idx;
        let mut implied: Option<Literal> = None;
        loop {
            self.clauses.bump_activity(current, 1);
            for i in 0..self.clauses.get_len(current) {
                let q = self.clauses.get_lit(current, i);
                if Some(q) == implied {
                    continue;
                }
                let var = q.unsigned_abs() as usize;
                if !self.seen[var] && self.levels[var] > 0 {
                    self.seen[var] = true;
                    touched.push(var);
                    self.bump_score(var);
                    if self.levels[var] >= self.current_level {
                        path += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            // Next literal of the current level to resolve on.
            loop {
                index -= 1;
                if self.seen[self.trail[index].unsigned_abs() as usize] {
                    break;
                }
            }
            let p = self.trail[index];
            let var = p.unsigned_abs() as usize;
            self.seen[var] = false;
            path -= 1;
            if path == 0 {
                learnt[0] = -p;
                break;
            }
            match self.reasons[var] {
                Some(reason) => {
                    current = reason;
                    implied = Some(p);
                }
                None => {
                    // A decision with other current-level literals pending cannot happen
                    // in a correct trail; stop with what we have rather than loop.
                    learnt[0] = -p;
                    break;
                }
            }
        }
        // Local minimisation: drop a literal whose reason is made of marked/level-0 literals.
        let mut kept = vec![learnt[0]];
        for &q in &learnt[1..] {
            let var = q.unsigned_abs() as usize;
            let redundant = match self.reasons[var] {
                None => false,
                Some(r) => (0..self.clauses.get_len(r)).all(|i| {
                    let l = self.clauses.get_lit(r, i);
                    let v = l.unsigned_abs() as usize;
                    v == var || self.seen[v] || self.levels[v] == 0
                }),
            };
            if !redundant {
                kept.push(q);
            }
        }
        for var in touched {
            self.seen[var] = false;
        }
        // Second literal: highest level among the rest (watch invariant).
        let mut backtrack_level = 0;
        if kept.len() > 1 {
            let mut best = 1;
            for i in 1..kept.len() {
                if self.levels[kept[i].unsigned_abs() as usize]
                    > self.levels[kept[best].unsigned_abs() as usize]
                {
                    best = i;
                }
            }
            kept.swap(1, best);
            backtrack_level = self.levels[kept[1].unsigned_abs() as usize];
        }
        (kept, backtrack_level)
    }
}

enum ConflictSource {
    Clause(ClauseIdx),
    Lits(Vec<Literal>),
}
