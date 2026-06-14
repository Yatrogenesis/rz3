use crate::ast::{Expr, ModelValue, Type};
use std::collections::BTreeMap;
use crate::theory::TheorySolver;
use num_rational::BigRational;
use num_bigint::BigInt;

type Rational = BigRational;

fn rat(numer: i64, denom: i64) -> Rational {
    BigRational::new(BigInt::from(numer), BigInt::from(denom))
}

fn int_rat(value: i64) -> Rational {
    BigRational::from_integer(BigInt::from(value))
}

fn decimal_rat(mantissa: i64, scale: u32) -> Rational {
    BigRational::new(BigInt::from(mantissa), BigInt::from(10u8).pow(scale))
}

#[derive(Debug, Clone)]
pub struct Bound {
    pub val: Rational,
    pub is_strict: bool,
}

/// Racional con infinitesimal simbólico positivo: `c + kδ`.
///
/// REF: [Dutertre & de Moura, 2006] "A Fast Linear-Arithmetic Solver for DPLL(T)"
///      DOI: 10.1007/11817963_11
///      Peer-reviewed: [Computer Aided Verification (CAV), ISSN: 0302-9743]
///      Validado contra: oráculos LRA de desigualdad y cotas estrictas estrechas.
/// Value in the ordered field ℚ(δ, ε): `c + kδ + Σ eps[i]·εᵢ`, where `1 ≫ δ ≫ ε₁ ≫ ε₂ ≫ …`
/// are independent positive infinitesimals. `δ` encodes strict inequalities (Dutertre–de
/// Moura). The `ε` layer is a **lexicographic perturbation by variable index** that breaks the
/// δ-pure degeneracy on which Bland's rule alone cycles (e.g. `x>y ∧ y>z ∧ z>x`), making the
/// feasibility Simplex terminate unconditionally. `eps` empty ⇒ identical to the old `c + kδ`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DeltaRational {
    c: Rational,
    k: Rational,
    eps: BTreeMap<usize, Rational>,
}

impl DeltaRational {
    fn rational(c: Rational) -> Self {
        Self { c, k: rat(0, 1), eps: BTreeMap::new() }
    }

    fn zero() -> Self {
        Self::rational(rat(0, 1))
    }

    /// `c + kδ + coef·ε_idx` — a single lexicographic perturbation on level `idx`.
    fn with_perturbation(c: Rational, k: i64, idx: usize, coef: Rational) -> Self {
        let mut eps = BTreeMap::new();
        if coef != rat(0, 1) { eps.insert(idx, coef); }
        Self { c, k: int_rat(k), eps }
    }

    fn add(&self, rhs: &Self) -> Self {
        let mut eps = self.eps.clone();
        for (i, v) in &rhs.eps {
            let e = eps.entry(*i).or_insert_with(|| rat(0, 1));
            *e += v.clone();
            if *e == rat(0, 1) { eps.remove(i); }
        }
        Self { c: self.c.clone() + rhs.c.clone(), k: self.k.clone() + rhs.k.clone(), eps }
    }

    fn sub(&self, rhs: &Self) -> Self {
        let mut eps = self.eps.clone();
        for (i, v) in &rhs.eps {
            let e = eps.entry(*i).or_insert_with(|| rat(0, 1));
            *e -= v.clone();
            if *e == rat(0, 1) { eps.remove(i); }
        }
        Self { c: self.c.clone() - rhs.c.clone(), k: self.k.clone() - rhs.k.clone(), eps }
    }

    fn scale(&self, a: Rational) -> Self {
        if a == rat(0, 1) { return Self::zero(); }
        let eps = self.eps.iter().map(|(i, v)| (*i, v.clone() * a.clone())).collect();
        Self { c: self.c.clone() * a.clone(), k: self.k.clone() * a, eps }
    }

    /// Total lexicographic order: `c`, then `kδ`, then `εᵢ` by ascending index (ε₁ dominates ε₂…).
    fn cmp_lex(&self, rhs: &Self) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        match self.c.cmp(&rhs.c) {
            Ordering::Equal => match self.k.cmp(&rhs.k) {
                Ordering::Equal => {
                    let zero = rat(0, 1);
                    // union of indices, ascending (BTreeMap keys are sorted)
                    let mut idxs: Vec<usize> = self.eps.keys().chain(rhs.eps.keys()).cloned().collect();
                    idxs.sort_unstable();
                    idxs.dedup();
                    for i in idxs {
                        let a = self.eps.get(&i).unwrap_or(&zero);
                        let b = rhs.eps.get(&i).unwrap_or(&zero);
                        match a.cmp(b) {
                            Ordering::Equal => continue,
                            ord => return ord,
                        }
                    }
                    Ordering::Equal
                }
                ord => ord,
            },
            ord => ord,
        }
    }

    fn lt_rational(&self, rhs: Rational) -> bool {
        self.cmp_lex(&DeltaRational::rational(rhs)) == core::cmp::Ordering::Less
    }

    fn le_rational(&self, rhs: Rational) -> bool {
        self.cmp_lex(&DeltaRational::rational(rhs)) != core::cmp::Ordering::Greater
    }

    fn lt_delta(&self, rhs: &Self) -> bool {
        self.cmp_lex(rhs) == core::cmp::Ordering::Less
    }

    fn min_delta(self, rhs: Self) -> Self {
        if self.lt_delta(&rhs) { self } else { rhs }
    }

    fn is_positive(&self) -> bool {
        self.cmp_lex(&DeltaRational::zero()) == core::cmp::Ordering::Greater
    }

    fn is_zero(&self) -> bool {
        self.c == rat(0, 1) && self.k == rat(0, 1) && self.eps.is_empty()
    }

    /// Drop the ε-perturbation, keeping the real value `c + kδ`. Used where the lexicographic
    /// tie-breaker must not leak into a real-value decision (e.g. disequality `≠` checks).
    fn real_part(&self) -> Self {
        Self { c: self.c.clone(), k: self.k.clone(), eps: BTreeMap::new() }
    }
}

/// Solver de Aritmética Lineal Real (LRA).
/// Utilizará una variante incremental del algoritmo Simplex con aritmética exacta.
// REF: [Dutertre & de Moura, 2006] "A Fast Linear-Arithmetic Solver for DPLL(T)"
//      DOI: 10.1007/11817963_11
//      Peer-reviewed: [Computer Aided Verification (CAV), ISSN: 0302-9743]
//      Validado contra: Benchmarks QF_LRA de SMT-LIB.
type Disequality = (BTreeMap<usize, Rational>, Rational, Expr);

/// Resultado de un intento de reparación de desigualdad (model-repair LRA).
enum RepairResult {
    /// Se movió una var (exacto, dentro de la región factible) rompiendo la igualdad.
    Moved,
    /// Ninguna var no-básica puede moverse en ninguna dirección: el politopo es un
    /// único punto -> la suma está forzada == target -> conflicto genuino (Unsat).
    FrozenPolytope,
    /// No se pudo romper, pero el politopo no es un punto -> no provablemente unsat -> Unknown.
    Stuck,
}

pub struct LraSolver {
    /// Mapeo de nombres de variables a IDs internos
    var_map: BTreeMap<String, usize>,
    /// Contador para nuevas variables (incluyendo slack vars)
    next_var_id: usize,
    /// Tableau: filas (variables básicas) -> columnas (variables no básicas -> coeficiente)
    tableau: BTreeMap<usize, BTreeMap<usize, Rational>>,
    /// Asignaciones actuales de las variables
    assignment: BTreeMap<usize, DeltaRational>,
    /// Límites inferiores (Lower bounds)
    lower_bounds: BTreeMap<usize, Bound>,
    /// Límites superiores (Upper bounds)
    upper_bounds: BTreeMap<usize, Bound>,
    /// Mapeo de variables básicas y no básicas
    basic_vars: Vec<usize>,
    non_basic_vars: Vec<usize>,
    /// Mapeo de variable y dirección del límite (true=lower, false=upper) -> Expresión original
    bound_origins: BTreeMap<(usize, bool), Expr>,
    /// Lista de desigualdades (a != b) que deben mantenerse: (coeffs, target_val, origin_expr)
    disequalities: Vec<Disequality>,
    /// Última variable que causó conflicto
    last_conflict_var: Option<usize>,
    /// Conflicto de desigualdad
    disequality_conflict: Option<Expr>,
    /// Orígenes de las cotas que congelan las vars de la desigualdad en conflicto genuino
    disequality_freeze_origins: Vec<Expr>,
    /// Pivot limit exceeded — result is Unknown, not Unsat
    is_unknown: bool,
    /// Origins of a same-linear-form bound conflict detected before the Simplex runs
    /// (see `detect_row_bound_conflict`). Non-empty ⇒ genuine UNSAT with these origins.
    bound_conflict: Vec<Expr>,
}

impl Default for LraSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl LraSolver {
    pub fn new() -> Self {
        Self {
            var_map: BTreeMap::new(),
            next_var_id: 0,
            tableau: BTreeMap::new(),
            assignment: BTreeMap::new(),
            lower_bounds: BTreeMap::new(),
            upper_bounds: BTreeMap::new(),
            basic_vars: Vec::new(),
            non_basic_vars: Vec::new(),
            bound_origins: BTreeMap::new(),
            disequalities: Vec::new(),
            last_conflict_var: None,
            disequality_conflict: None,
            disequality_freeze_origins: Vec::new(),
            is_unknown: false,
            bound_conflict: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        self.var_map.clear();
        self.next_var_id = 0;
        self.tableau.clear();
        self.assignment.clear();
        self.lower_bounds.clear();
        self.upper_bounds.clear();
        self.basic_vars.clear();
        self.non_basic_vars.clear();
        self.bound_origins.clear();
        self.disequalities.clear();
        self.last_conflict_var = None;
        self.disequality_conflict = None;
        self.disequality_freeze_origins.clear();
        self.is_unknown = false;
        self.bound_conflict.clear();
    }

    pub fn is_unknown(&self) -> bool {
        self.is_unknown
    }

    /// Returns user-declared variable assignments for model extraction.
    pub fn get_all_assignments(&self) -> Vec<(String, BigRational)> {
        let delta = self.model_delta();
        self.var_map.iter()
            .filter_map(|(name, &id)| {
                self.assignment.get(&id).map(|value| {
                    let ratio = value.c.clone() + value.k.clone() * delta.clone();
                    (name.clone(), ratio)
                })
            })
            .collect()
    }

    fn get_or_create_var(&mut self, name: &str) -> usize {
        if let Some(&id) = self.var_map.get(name) {
            id
        } else {
            let id = self.next_var_id;
            self.var_map.insert(name.to_string(), id);
            self.next_var_id += 1;
            self.non_basic_vars.push(id);
            self.assignment.insert(id, DeltaRational::zero());
            id
        }
    }

    fn create_slack_var(&mut self) -> usize {
        let id = self.next_var_id;
        self.next_var_id += 1;
        self.assignment.insert(id, DeltaRational::zero());
        id
    }

    fn update(&mut self, x_j: usize, v: DeltaRational) {
        let diff = v.sub(self.assignment.get(&x_j).unwrap_or(&DeltaRational::zero()));
        self.assignment.insert(x_j, v);
        
        for (&x_i, row) in self.tableau.iter() {
            if let Some(a_ij) = row.get(&x_j) {
                let current_val = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
                self.assignment.insert(x_i, current_val.add(&diff.scale(a_ij.clone())));
            }
        }
    }

    pub fn pivot(&mut self, x_i: usize, x_j: usize) {
        let Some(row) = self.tableau.remove(&x_i) else {
            self.is_unknown = true;
            return;
        };
        let Some(a_ij) = row.get(&x_j).cloned() else {
            self.tableau.insert(x_i, row);
            self.is_unknown = true;
            return;
        };

        let mut new_row = BTreeMap::new();
        new_row.insert(x_i, rat(1, 1) / a_ij.clone());
        for (&col, val) in row.iter() {
            if col != x_j {
                new_row.insert(col, -val.clone() / a_ij.clone());
            }
        }

        for (_basic, other_row) in self.tableau.iter_mut() {
            if let Some(a_ik) = other_row.remove(&x_j) {
                for (&col, val) in new_row.iter() {
                    let entry = other_row.entry(col).or_insert(rat(0, 1));
                    *entry += a_ik.clone() * val.clone();
                }
            }
        }

        self.tableau.insert(x_j, new_row);
        
        if let Some(pos) = self.basic_vars.iter().position(|&v| v == x_i) {
            self.basic_vars[pos] = x_j;
        }
        if let Some(pos) = self.non_basic_vars.iter().position(|&v| v == x_j) {
            self.non_basic_vars[pos] = x_i;
        }
    }

    /// Sound, additive pre-Simplex check: detect UNSAT arising from two bounds on the
    /// SAME linear form (up to a positive scalar / sign) being contradictory — including
    /// the strict-equality case `lower == upper ∧ (lower.strict ∨ upper.strict)`.
    ///
    /// Each asserted constraint gets a FRESH slack (`create_slack_var`), so e.g. `x>0`
    /// and `x<0` produce two distinct slacks over the row `{x:1}` carrying `lower 0
    /// (strict)` and `upper 0 (strict)`. The feasibility Simplex then oscillates between
    /// those slacks (a state de Moura's invariants exclude, because it never duplicates a
    /// linear form) and exhausts its pivot budget → `Unknown` instead of `Unsat`.
    ///
    /// To catch this regardless of scaling or orientation, each slack's row is reduced to
    /// a CANONICAL form: divide by the leading (lowest-index) coefficient so the leading
    /// coefficient becomes 1. Dividing by a NEGATIVE leading coefficient flips the
    /// inequality, so the bound is mapped lower↔upper, value scaled, strictness preserved
    /// (`y−x > 0` ≡ `x−y < 0`). Rows that are positive/negative scalar multiples of each
    /// other thus collapse to the same key, and `2x>0 ∧ x<0` or `x>y ∧ y>x` become
    /// immediate, sound conflicts. Genuinely multi-row infeasibilities (e.g. the Farkas
    /// cycle `x>y ∧ y>z ∧ z>x`) are NOT same-form and fall through to the Simplex (→ sound
    /// `Unknown`); this check never emits a wrong verdict.
    fn detect_row_bound_conflict(&mut self) -> bool {
        // canonical_key → (tightest_lower, tightest_upper); each as (value, strict, slack, orig_is_lower).
        type B = (Rational, bool, usize, bool);
        type Tight = (Option<B>, Option<B>);
        let mut groups: BTreeMap<Vec<(usize, Rational)>, Tight> = BTreeMap::new();

        for (&slack, row) in &self.tableau {
            let Some((&_lead, lead_coeff)) = row.iter().next() else { continue }; // empty row → skip
            if *lead_coeff == rat(0, 1) { continue; }
            let factor = lead_coeff.clone();
            let flip = factor < rat(0, 1);
            let key: Vec<(usize, Rational)> =
                row.iter().map(|(&v, c)| (v, c.clone() / factor.clone())).collect();

            // Map this slack's lower/upper into canonical orientation.
            // `orig_is_lower` records the original direction for origin lookup.
            let scale = |b: &Bound| (b.val.clone() / factor.clone(), b.is_strict);
            let canon_lower: Option<B>; // becomes lower bound of the canonical form
            let canon_upper: Option<B>;
            if flip {
                // dividing by a negative flips direction: original lower → canonical upper
                canon_upper = self.lower_bounds.get(&slack).map(|b| { let (v, s) = scale(b); (v, s, slack, true) });
                canon_lower = self.upper_bounds.get(&slack).map(|b| { let (v, s) = scale(b); (v, s, slack, false) });
            } else {
                canon_lower = self.lower_bounds.get(&slack).map(|b| { let (v, s) = scale(b); (v, s, slack, true) });
                canon_upper = self.upper_bounds.get(&slack).map(|b| { let (v, s) = scale(b); (v, s, slack, false) });
            }

            let entry = groups.entry(key).or_insert((None, None));
            if let Some(cl) = canon_lower {
                let tighter = match &entry.0 {
                    None => true,
                    Some((cv, cs, _, _)) => cl.0 > *cv || (cl.0 == *cv && cl.1 && !*cs),
                };
                if tighter { entry.0 = Some(cl); }
            }
            if let Some(cu) = canon_upper {
                let tighter = match &entry.1 {
                    None => true,
                    Some((cv, cs, _, _)) => cu.0 < *cv || (cu.0 == *cv && cu.1 && !*cs),
                };
                if tighter { entry.1 = Some(cu); }
            }
        }

        for (_key, (lo, hi)) in &groups {
            if let (Some((lv, ls, lslack, lorig)), Some((uv, us, uslack, uorig))) = (lo, hi) {
                if lv > uv || (lv == uv && (*ls || *us)) {
                    let mut origins = Vec::new();
                    if let Some(e) = self.bound_origins.get(&(*lslack, *lorig)) { origins.push(e.clone()); }
                    if let Some(e) = self.bound_origins.get(&(*uslack, *uorig)) { origins.push(e.clone()); }
                    self.bound_conflict = origins;
                    return true;
                }
            }
        }
        false
    }

    /// Sound, additive pre-Simplex decision for the **Difference-Logic fragment**:
    /// constraints of the form `±x ∓ y OP c` (and single-variable bounds `x OP c`).
    /// Their joint infeasibility is exactly a **negative cycle** in the constraint graph,
    /// decided here by Bellman-Ford. This is the textbook DL decision procedure and is
    /// the fragment on which the feasibility Simplex cycles when all variables are free
    /// (e.g. `x>y ∧ y>z ∧ z>x` — a strict zero cycle the Simplex can't settle → Unknown).
    ///
    /// Each qualifying slack contributes one edge per bound (lower/upper). A constraint
    /// `pos − neg ≥ k` becomes edge `pos → neg` of weight `−k`; `pos − neg ≤ k` becomes
    /// `neg → pos` of weight `k`; single-variable bounds use a fixed zero node. Strictness
    /// is carried as a `−δ` term (DeltaRational), so a zero-weight cycle is a negative
    /// cycle iff it has ≥1 strict edge — `x≥y ∧ y≥z ∧ z≥x` (all non-strict) stays SAT.
    /// Rows that are NOT differences (sums like `x+y`, ≥3 vars, mismatched coefficients)
    /// are skipped — never turned into edges — so this can only ever report a genuine
    /// negative cycle (sound: no false UNSAT). Self-contained Bellman-Ford keeps r-z3's
    /// zero-extra-dependency / WASM-lean property.
    fn detect_difference_logic_conflict(&mut self) -> bool {
        const ZERO: usize = usize::MAX; // node representing the constant 0
        // edges: (from, to, weight, origin)
        let mut edges: Vec<(usize, usize, DeltaRational, Expr)> = Vec::new();
        let mut nodes: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        let zero = rat(0, 1);

        for (&slack, row) in &self.tableau {
            let entries: Vec<(usize, Rational)> = row
                .iter()
                .filter(|(_, c)| **c != zero)
                .map(|(&v, c)| (v, c.clone()))
                .collect();

            // Reduce the row to `factor * (pos - neg)` with factor > 0, or skip if not DL.
            let (pos, neg, factor): (usize, usize, Rational) = match entries.as_slice() {
                [(v, c)] => {
                    if *c > zero { (*v, ZERO, c.clone()) } else { (ZERO, *v, -c.clone()) }
                }
                [(v1, c1), (v2, c2)] if *c1 == -c2.clone() => {
                    if *c1 > zero { (*v1, *v2, c1.clone()) } else { (*v2, *v1, c2.clone()) }
                }
                _ => continue, // not a difference-logic atom
            };

            // lower l : factor*(pos-neg) ≥ l  →  pos-neg ≥ l/factor  →  edge pos→neg, w = -(l/factor)
            if let Some(lb) = self.lower_bounds.get(&slack) {
                if let Some(o) = self.bound_origins.get(&(slack, true)) {
                    let k = -(lb.val.clone() / factor.clone());
                    let w = DeltaRational { c: k, k: if lb.is_strict { -rat(1, 1) } else { zero.clone() }, eps: BTreeMap::new() };
                    edges.push((pos, neg, w, o.clone()));
                    nodes.insert(pos);
                    nodes.insert(neg);
                }
            }
            // upper u : factor*(pos-neg) ≤ u  →  pos-neg ≤ u/factor  →  edge neg→pos, w = u/factor
            if let Some(ub) = self.upper_bounds.get(&slack) {
                if let Some(o) = self.bound_origins.get(&(slack, false)) {
                    let k = ub.val.clone() / factor.clone();
                    let w = DeltaRational { c: k, k: if ub.is_strict { -rat(1, 1) } else { zero.clone() }, eps: BTreeMap::new() };
                    edges.push((neg, pos, w, o.clone()));
                    nodes.insert(neg);
                    nodes.insert(pos);
                }
            }
        }

        if edges.is_empty() {
            return false;
        }

        // Bellman-Ford with a virtual source (all distances init 0) to find any negative
        // cycle. With `n` nodes, a cycle-free graph settles in ≤ n-1 passes; if pass `n`
        // still relaxes, a negative cycle exists.
        let n = nodes.len();
        let mut dist: BTreeMap<usize, DeltaRational> =
            nodes.iter().map(|&v| (v, DeltaRational::zero())).collect();
        let mut pred: BTreeMap<usize, (usize, usize)> = BTreeMap::new(); // node → (pred, edge_idx)
        let mut last_relaxed: Option<usize> = None;

        for _ in 0..n {
            let mut relaxed_this_pass = false;
            for (idx, (u, v, w, _)) in edges.iter().enumerate() {
                let cand = dist[u].add(w);
                if cand.lt_delta(&dist[v]) {
                    dist.insert(*v, cand);
                    pred.insert(*v, (*u, idx));
                    relaxed_this_pass = true;
                    last_relaxed = Some(*v);
                }
            }
            if !relaxed_this_pass {
                return false; // settled, no negative cycle
            }
        }

        // Negative cycle present. Walk back n steps to land inside it, then collect the
        // cycle's edge origins (best-effort; the verdict is sound regardless).
        let Some(mut cur) = last_relaxed else { return false };
        for _ in 0..n {
            cur = pred[&cur].0;
        }
        let entry = cur;
        let mut origins = Vec::new();
        let mut guard = 0;
        loop {
            let (p, idx) = pred[&cur];
            origins.push(edges[idx].3.clone());
            cur = p;
            guard += 1;
            if cur == entry || guard > n {
                break;
            }
        }
        self.bound_conflict = origins;
        true
    }

    /// Lower bound of `v` in ℚ(δ,ε): `l (+δ if strict) − ε_v`. The `−ε_v` is a lexicographic
    /// perturbation unique to `v`'s index; relaxing every bound by an independent infinitesimal
    /// `ε ≪ δ` removes the degeneracy that makes the feasibility Simplex cycle, while preserving
    /// the SAT/UNSAT verdict in the limit `ε→0⁺` (δ dominates ε, so strict-bound conflicts stand).
    fn perturbed_lower(&self, v: usize) -> Option<DeltaRational> {
        self.lower_bounds.get(&v).map(|b|
            DeltaRational::with_perturbation(b.val.clone(), if b.is_strict { 1 } else { 0 }, v, rat(-1, 1)))
    }
    /// Upper bound of `v`: `u (−δ if strict) + ε_v` (relaxed upward by the same perturbation).
    fn perturbed_upper(&self, v: usize) -> Option<DeltaRational> {
        self.upper_bounds.get(&v).map(|b|
            DeltaRational::with_perturbation(b.val.clone(), if b.is_strict { -1 } else { 0 }, v, rat(1, 1)))
    }

    pub fn check_feasibility(&mut self) -> bool {
        // Decide two fragments directly, outside the fragile feasibility Simplex:
        //   (1) same-linear-form bound conflicts (canonical row), and
        //   (2) the difference-logic fragment (negative cycle).
        // Both are sound; the Simplex still handles general multi-row LRA below.
        if self.detect_row_bound_conflict() {
            return false;
        }
        if self.detect_difference_logic_conflict() {
            return false;
        }
        let mut pivots = 0;
        let max_pivots = 2000;
        let mut diseq_repairs = 0usize;
        let max_diseq_repairs = 2000usize;

        loop {
            if pivots > max_pivots {
                // Pivot budget exhausted — result is Unknown, not Sat.
                // Caller must check is_unknown() before trusting the return value.
                self.is_unknown = true;
                return true;
            }
            pivots += 1;

            let mut violated_var = None;
            let mut basic_vars_sorted = self.basic_vars.clone();
            basic_vars_sorted.sort_unstable();

            for &x_i in &basic_vars_sorted {
                let val = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
                // Compare against the lexicographically-perturbed bound (l+δ−ε_i / u−δ+ε_i),
                // so strict bounds AND the ε-perturbation are honoured in one total order.
                if let Some(pl) = self.perturbed_lower(x_i) {
                    if val.cmp_lex(&pl) == core::cmp::Ordering::Less {
                        violated_var = Some((x_i, true));
                        break;
                    }
                }
                if let Some(pu) = self.perturbed_upper(x_i) {
                    if val.cmp_lex(&pu) == core::cmp::Ordering::Greater {
                        violated_var = Some((x_i, false));
                        break;
                    }
                }
            }

            if let Some((x_i, is_lower)) = violated_var {
                let mut found_pivot = false;
                
                // Bland's rule: sort variables to ensure deterministic, low-index selection
                let mut non_basic_vars = self.non_basic_vars.clone();
                non_basic_vars.sort_unstable();

                // Move the violated variable exactly to its perturbed bound — this is what
                // makes each landing point unique and breaks the δ-pure degeneracy.
                let target_val = if is_lower {
                    self.perturbed_lower(x_i).unwrap()
                } else {
                    self.perturbed_upper(x_i).unwrap()
                };

                for &x_j in &non_basic_vars {
                    let row = &self.tableau[&x_i];
                    let a_ij = row.get(&x_j).cloned().unwrap_or_else(|| rat(0, 1));
                    if a_ij == rat(0, 1) { continue; }

                    let val_j = self.assignment.get(&x_j).cloned().unwrap_or_else(DeltaRational::zero);

                    let can_increase = if let Some(pu) = self.perturbed_upper(x_j) {
                        val_j.cmp_lex(&pu) == core::cmp::Ordering::Less
                    } else { true };
                    let can_decrease = if let Some(pl) = self.perturbed_lower(x_j) {
                        val_j.cmp_lex(&pl) == core::cmp::Ordering::Greater
                    } else { true };

                    let a_ij_gt_0 = a_ij > rat(0, 1);
                    let improves = if is_lower {
                        (a_ij_gt_0 && can_increase) || (!a_ij_gt_0 && can_decrease)
                    } else {
                        (a_ij_gt_0 && can_decrease) || (!a_ij_gt_0 && can_increase)
                    };

                    if improves {
                        self.pivot(x_i, x_j);
                        self.update(x_i, target_val.clone());
                        found_pivot = true;
                        break;
                    }
                }
                if !found_pivot {
                    self.last_conflict_var = Some(x_i);
                    return false;
                }
            } else {
                // Factible respecto a cotas. Revisar desigualdades (≠).
                // En violación: model-repair SOUND y acotado (perturbar una var NO
                // básica por un racional EXACTO dentro de sus cotas). Si no hay
                // reparación y la suma es provablemente constante (todas las vars
                // pinned lb==ub) -> conflicto genuino (Unsat). Si no es provable o se
                // agota el presupuesto -> Unknown (sound). [Dutertre-deMoura + advisor].
                let mut violated_idx = None;
                for (idx, (coeffs, target, _)) in self.disequalities.iter().enumerate() {
                    let mut current_sum = DeltaRational::zero();
                    for (&var, coeff) in coeffs {
                        let val = self.assignment.get(&var).cloned().unwrap_or_else(DeltaRational::zero);
                        current_sum = current_sum.add(&val.scale(coeff.clone()));
                    }
                    // The ε-perturbation is only a tie-breaker for the bounds Simplex; a
                    // disequality `Σ≠target` is about the REAL value, so compare on the
                    // `c+kδ` part with ε projected out (otherwise a pinned `x=1` looks like
                    // `1±ε ≠ 1` and the genuine `x≠1` conflict is missed → false SAT).
                    if current_sum.real_part() == DeltaRational::rational(target.clone()) { violated_idx = Some(idx); break; }
                }
                match violated_idx {
                    None => return true,
                    Some(idx) => {
                        diseq_repairs += 1;
                        if diseq_repairs > max_diseq_repairs {
                            self.is_unknown = true;
                            return true; // Unknown (sound)
                        }
                        match self.try_repair_disequality(idx) {
                            RepairResult::Moved => continue, // re-escanear cotas + desigualdades
                            RepairResult::FrozenPolytope => {
                                // Único punto factible: la suma está forzada == target -> Unsat genuino.
                                self.disequality_conflict = Some(self.disequalities[idx].2.clone());
                                self.collect_freeze_origins(idx);
                                return false;
                            }
                            RepairResult::Stuck => {
                                // No reparable, pero el politopo no es un punto -> Unknown (sound).
                                self.is_unknown = true;
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }

    /// Máximo movimiento factible (exacto) de la var no-básica `x_j` hacia arriba y
    /// hacia abajo, manteniendo TODAS las vars básicas dentro de sus cotas (ratio test
    /// de Simplex). `None` = sin cota (∞). Asume la asignación actual factible (room>=0).
    fn feasible_room(&self, x_j: usize) -> (Option<DeltaRational>, Option<DeltaRational>) {
        let zero = rat(0, 1);
        let val_j = self.assignment.get(&x_j).cloned().unwrap_or_else(DeltaRational::zero);
        let mut up: Option<DeltaRational> = self.upper_bounds.get(&x_j)
            .map(|b| DeltaRational { c: b.val.clone() - val_j.c.clone(), k: -val_j.k.clone(), eps: BTreeMap::new() });
        let mut down: Option<DeltaRational> = self.lower_bounds.get(&x_j)
            .map(|b| DeltaRational { c: val_j.c.clone() - b.val.clone(), k: val_j.k.clone(), eps: BTreeMap::new() });
        for (&x_i, row) in self.tableau.iter() {
            let a_ij = match row.get(&x_j) { Some(a) if *a != zero => a.clone(), _ => continue };
            let val_i = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
            // Subir x_j por Δ mueve x_i por a_ij*Δ.
            if a_ij > zero {
                if let Some(ub) = self.upper_bounds.get(&x_i) {
                    let room = DeltaRational { c: ub.val.clone() - val_i.c.clone(), k: -val_i.k.clone(), eps: BTreeMap::new() }.scale(rat(1, 1) / a_ij.clone());
                    up = Some(up.map_or(room.clone(), |u| u.min_delta(room)));
                }
                if let Some(lb) = self.lower_bounds.get(&x_i) {
                    let room = DeltaRational { c: val_i.c.clone() - lb.val.clone(), k: val_i.k.clone(), eps: BTreeMap::new() }.scale(rat(1, 1) / a_ij.clone());
                    down = Some(down.map_or(room.clone(), |d| d.min_delta(room)));
                }
            } else {
                let neg = -a_ij;
                if let Some(lb) = self.lower_bounds.get(&x_i) {
                    let room = DeltaRational { c: val_i.c.clone() - lb.val.clone(), k: val_i.k.clone(), eps: BTreeMap::new() }.scale(rat(1, 1) / neg.clone());
                    up = Some(up.map_or(room.clone(), |u| u.min_delta(room)));
                }
                if let Some(ub) = self.upper_bounds.get(&x_i) {
                    let room = DeltaRational { c: ub.val.clone() - val_i.c.clone(), k: -val_i.k.clone(), eps: BTreeMap::new() }.scale(rat(1, 1) / neg.clone());
                    down = Some(down.map_or(room.clone(), |d| d.min_delta(room)));
                }
            }
        }
        (up, down)
    }

    /// Repara la desigualdad violada `idx`: mueve (exacto) una var no-básica con efecto
    /// no nulo sobre la suma, dentro de la región factible (ratio test). Determinista
    /// (por índice). Si ninguna var puede moverse en ninguna dirección -> politopo = punto.
    fn try_repair_disequality(&mut self, idx: usize) -> RepairResult {
        let coeffs = self.disequalities[idx].0.clone();
        let zero = rat(0, 1);
        let one = rat(1, 1);
        let mut nb = self.non_basic_vars.clone();
        nb.sort_unstable();
        let mut any_can_move = false;
        let mut mover: Option<(usize, DeltaRational)> = None;
        for &x_j in &nb {
            let (up, down) = self.feasible_room(x_j);
            let can_up = up.as_ref().is_none_or(DeltaRational::is_positive);
            let can_down = down.as_ref().is_none_or(DeltaRational::is_positive);
            if can_up || can_down { any_can_move = true; }
            if mover.is_none() {
                // r_j = d(sum)/d(x_j): coef propio + Σ_{v básica en coeffs} coef_v * tableau[v][x_j]
                let mut r_j = coeffs.get(&x_j).cloned().unwrap_or_else(|| zero.clone());
                for (&v, c_v) in &coeffs {
                    if let Some(row) = self.tableau.get(&v) {
                        if let Some(a_vj) = row.get(&x_j) { r_j += c_v.clone() * a_vj.clone(); }
                    }
                }
                if r_j != zero {
                    // Cualquier Δ≠0 factible rompe la igualdad (r_j≠0). Paso exacto acotado.
                    let delta = if can_up {
                        match up.clone() {
                            Some(r) if r.c > zero => DeltaRational::rational(r.c.min(one.clone())),
                            Some(r) => DeltaRational { c: zero.clone(), k: r.k / rat(2, 1), eps: BTreeMap::new() },
                            None => DeltaRational::rational(one.clone()),
                        }
                    } else if can_down {
                        match down.clone() {
                            Some(r) if r.c > zero => DeltaRational::rational(-(r.c.min(one.clone()))),
                            Some(r) => DeltaRational { c: zero.clone(), k: -(r.k / rat(2, 1)), eps: BTreeMap::new() },
                            None => DeltaRational::rational(-one.clone()),
                        }
                    } else { DeltaRational::zero() };
                    if !delta.is_zero() { mover = Some((x_j, delta)); }
                }
            }
        }
        if let Some((x_j, delta)) = mover {
            let val_j = self.assignment.get(&x_j).cloned().unwrap_or_else(DeltaRational::zero);
            self.update(x_j, val_j.add(&delta));
            return RepairResult::Moved;
        }
        if any_can_move { RepairResult::Stuck } else { RepairResult::FrozenPolytope }
    }

    /// Guarda los orígenes de las cotas que congelan las variables de la desigualdad
    /// en conflicto, para una explicación completa al SAT core.
    fn collect_freeze_origins(&mut self, idx: usize) {
        self.disequality_freeze_origins.clear();
        let vars: Vec<usize> = self.disequalities[idx].0.keys().copied().collect();
        for v in vars {
            if let Some(e) = self.bound_origins.get(&(v, true)) { self.disequality_freeze_origins.push(e.clone()); }
            if let Some(e) = self.bound_origins.get(&(v, false)) { self.disequality_freeze_origins.push(e.clone()); }
        }
    }

    fn model_delta(&self) -> Rational {
        let zero = rat(0, 1);
        let mut upper: Option<Rational> = None;
        for (&var, value) in &self.assignment {
            if value.k > zero {
                if let Some(ub) = self.upper_bounds.get(&var) {
                    if ub.val > value.c {
                        let limit = (ub.val.clone() - value.c.clone()) / value.k.clone();
                        upper = Some(upper.map_or(limit.clone(), |current| current.min(limit)));
                    }
                }
            } else if value.k < zero {
                if let Some(lb) = self.lower_bounds.get(&var) {
                    if value.c > lb.val {
                        let limit = (value.c.clone() - lb.val.clone()) / -value.k.clone();
                        upper = Some(upper.map_or(limit.clone(), |current| current.min(limit)));
                    }
                }
            }
        }
        match upper {
            Some(limit) if limit > zero => limit / rat(2, 1),
            _ => rat(1, 1),
        }
    }
}

impl TheorySolver for LraSolver {
    fn assert(&mut self, expr: &Expr) {
        // ... (existing implementation)
        match expr {
            Expr::Not(inner) => {
                match &**inner {
                    Expr::Le(lhs, rhs) => self.assert_internal(&Expr::Gt(lhs.clone(), rhs.clone()), expr),
                    Expr::Ge(lhs, rhs) => self.assert_internal(&Expr::Lt(lhs.clone(), rhs.clone()), expr),
                    Expr::Lt(lhs, rhs) => self.assert_internal(&Expr::Ge(lhs.clone(), rhs.clone()), expr),
                    Expr::Gt(lhs, rhs) => self.assert_internal(&Expr::Le(lhs.clone(), rhs.clone()), expr),
                    Expr::Eq(lhs, rhs) => {
                        let mut coeffs = BTreeMap::new();
                        let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                        let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                        self.disequalities.push((coeffs, -(c1 + c2), expr.clone()));
                    }
                    _ => {}
                }
            }
            _ => self.assert_internal(expr, expr),
        }
    }

    fn check(&mut self) -> bool {
        self.check_feasibility()
    }

    fn explain(&self) -> Vec<Expr> {
        if !self.bound_conflict.is_empty() {
            // Same-linear-form bound conflict (detect_row_bound_conflict): the two
            // contradictory bound origins are exactly the unsat core.
            return self.bound_conflict.clone();
        }
        if let Some(origin) = &self.disequality_conflict {
            // Origen de la desigualdad + las cotas que congelan sus variables,
            // para que el SAT core aprenda una cláusula útil (no una trivial).
            let mut out = vec![origin.clone()];
            out.extend(self.disequality_freeze_origins.iter().cloned());
            return out;
        }

        let mut conflict = Vec::new();
        if let Some(x_i) = self.last_conflict_var {
            let val_i = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
            let is_lower_violated = if let Some(lb) = self.lower_bounds.get(&x_i) {
                val_i.lt_rational(lb.val.clone()) || (lb.is_strict && val_i.le_rational(lb.val.clone()))
            } else { false };

            if let Some(expr) = self.bound_origins.get(&(x_i, is_lower_violated)) {
                conflict.push(expr.clone());
            }

            if let Some(row) = self.tableau.get(&x_i) {
                for (&x_j, a_ij) in row.iter() {
                    let a_ij_gt_0 = a_ij > &rat(0, 1);
                    let needed_lower = if is_lower_violated { !a_ij_gt_0 } else { a_ij_gt_0 };
                    if let Some(expr) = self.bound_origins.get(&(x_j, needed_lower)) {
                        conflict.push(expr.clone());
                    }
                }
            }
        }
        conflict
    }

    fn get_model_value(&self, expr: &Expr) -> Option<ModelValue> {
        if let Expr::Var(name, Type::Real) = expr {
            if let Some(&id) = self.var_map.get(name) {
                if let Some(val) = self.assignment.get(&id) {
                    let delta = self.model_delta();
                    let concrete = val.c.clone() + val.k.clone() * delta;
                    return Some(ModelValue::Real(concrete)); // exacto
                }
            }
        }
        None
    }
}

impl LraSolver {
    fn assert_internal(&mut self, rel_expr: &Expr, origin_expr: &Expr) {
        match rel_expr {
            Expr::Le(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.upper_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            Expr::Lt(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.upper_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: true });
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            Expr::Ge(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.bound_origins.insert((slack, true), origin_expr.clone());
            }
            Expr::Gt(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: true });
                self.bound_origins.insert((slack, true), origin_expr.clone());
            }
            Expr::Eq(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, rat(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, rat(-1, 1), &mut coeffs);
                let bound = -(c1 + c2);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: bound.clone(), is_strict: false });
                self.upper_bounds.insert(slack, Bound { val: bound, is_strict: false });
                self.bound_origins.insert((slack, true), origin_expr.clone());
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            _ => {}
        }
    }

    fn extract_coeffs(&mut self, expr: &Expr, scale: Rational, coeffs: &mut BTreeMap<usize, Rational>) -> Rational {
        match expr {
            Expr::Int(i) => scale * int_rat(*i),
            Expr::Real(i, s) => scale * decimal_rat(*i, *s),
            Expr::Var(name, _) => {
                let id = self.get_or_create_var(name);
                *coeffs.entry(id).or_insert(rat(0, 1)) += scale;
                rat(0, 1)
            }
            Expr::Add(args) => {
                let mut constant = rat(0, 1);
                for arg in args {
                    constant += self.extract_coeffs(arg, scale.clone(), coeffs);
                }
                constant
            }
            Expr::Sub(args) => {
                if args.is_empty() { return rat(0, 1); }
                let mut constant = self.extract_coeffs(&args[0], scale.clone(), coeffs);
                for arg in &args[1..] {
                    // Subtrahend must be extracted with NEGATED scale so its *variables*
                    // get the right sign, not only the returned constant. The previous
                    // `constant -= extract(arg, scale)` was correct for constants but left
                    // subtrahend variables with the wrong sign — `x - y` became `x + y`.
                    constant += self.extract_coeffs(arg, -scale.clone(), coeffs);
                }
                constant
            }
            Expr::Mul(args) => {
                if args.len() == 2 {
                    if let Some(c) = self.try_eval_const(&args[0]) {
                        return self.extract_coeffs(&args[1], scale * c, coeffs);
                    } else if let Some(c) = self.try_eval_const(&args[1]) {
                        return self.extract_coeffs(&args[0], scale * c, coeffs);
                    }
                }
                // Fallthrough to treat as uninterpreted variable
                let id = self.get_or_create_var(&format!("{}", expr));
                *coeffs.entry(id).or_insert(rat(0, 1)) += scale;
                rat(0, 1)
            }
            _ => {
                let id = self.get_or_create_var(&format!("{}", expr));
                *coeffs.entry(id).or_insert(rat(0, 1)) += scale;
                rat(0, 1)
            }
        }
    }

    fn try_eval_const(&self, expr: &Expr) -> Option<Rational> {
        match expr {
            Expr::Int(i) => Some(int_rat(*i)),
            Expr::Real(i, s) => Some(decimal_rat(*i, *s)),
            _ => None,
        }
    }
}

