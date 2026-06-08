use crate::ast::{Expr, ModelValue, Type};
use std::collections::BTreeMap;
use crate::theory::TheorySolver;
use num_rational::{Ratio, BigRational};
use num_bigint::BigInt;

#[derive(Debug, Clone)]
pub struct Bound {
    pub val: Ratio<i64>,
    pub is_strict: bool,
}

/// Racional con infinitesimal simbólico positivo: `c + kδ`.
///
/// REF: [Dutertre & de Moura, 2006] "A Fast Linear-Arithmetic Solver for DPLL(T)"
///      DOI: 10.1007/11817963_11
///      Peer-reviewed: [Computer Aided Verification (CAV), ISSN: 0302-9743]
///      Validado contra: oráculos LRA de desigualdad y cotas estrictas estrechas.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DeltaRational {
    c: Ratio<i64>,
    k: Ratio<i64>,
}

impl DeltaRational {
    fn rational(c: Ratio<i64>) -> Self {
        Self { c, k: Ratio::new(0, 1) }
    }

    fn delta_shift(c: Ratio<i64>, k: i64) -> Self {
        Self { c, k: Ratio::new(k, 1) }
    }

    fn zero() -> Self {
        Self::rational(Ratio::new(0, 1))
    }

    fn add(&self, rhs: &Self) -> Self {
        Self { c: self.c + rhs.c, k: self.k + rhs.k }
    }

    fn sub(&self, rhs: &Self) -> Self {
        Self { c: self.c - rhs.c, k: self.k - rhs.k }
    }

    fn scale(&self, a: Ratio<i64>) -> Self {
        Self { c: self.c * a, k: self.k * a }
    }

    fn lt_rational(&self, rhs: Ratio<i64>) -> bool {
        self.c < rhs || (self.c == rhs && self.k < Ratio::new(0, 1))
    }

    fn le_rational(&self, rhs: Ratio<i64>) -> bool {
        self.c < rhs || (self.c == rhs && self.k <= Ratio::new(0, 1))
    }

    fn gt_rational(&self, rhs: Ratio<i64>) -> bool {
        self.c > rhs || (self.c == rhs && self.k > Ratio::new(0, 1))
    }

    fn ge_rational(&self, rhs: Ratio<i64>) -> bool {
        self.c > rhs || (self.c == rhs && self.k >= Ratio::new(0, 1))
    }

    fn lt_delta(&self, rhs: &Self) -> bool {
        self.c < rhs.c || (self.c == rhs.c && self.k < rhs.k)
    }

    fn min_delta(self, rhs: Self) -> Self {
        if self.lt_delta(&rhs) { self } else { rhs }
    }

    fn is_positive(&self) -> bool {
        self.c > Ratio::new(0, 1) || (self.c == Ratio::new(0, 1) && self.k > Ratio::new(0, 1))
    }

    fn is_zero(&self) -> bool {
        self.c == Ratio::new(0, 1) && self.k == Ratio::new(0, 1)
    }
}

/// Solver de Aritmética Lineal Real (LRA).
/// Utilizará una variante incremental del algoritmo Simplex con aritmética exacta.
// REF: [Dutertre & de Moura, 2006] "A Fast Linear-Arithmetic Solver for DPLL(T)"
//      DOI: 10.1007/11817963_11
//      Peer-reviewed: [Computer Aided Verification (CAV), ISSN: 0302-9743]
//      Validado contra: Benchmarks QF_LRA de SMT-LIB.
type Disequality = (BTreeMap<usize, Ratio<i64>>, Ratio<i64>, Expr);

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
    tableau: BTreeMap<usize, BTreeMap<usize, Ratio<i64>>>,
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
                    let ratio = value.c + value.k * delta;
                    let r = BigRational::new(BigInt::from(*ratio.numer()), BigInt::from(*ratio.denom()));
                    (name.clone(), r)
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
            if let Some(&a_ij) = row.get(&x_j) {
                let current_val = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
                self.assignment.insert(x_i, current_val.add(&diff.scale(a_ij)));
            }
        }
    }

    pub fn pivot(&mut self, x_i: usize, x_j: usize) {
        let row = self.tableau.remove(&x_i).unwrap();
        let a_ij = *row.get(&x_j).unwrap();

        let mut new_row = BTreeMap::new();
        new_row.insert(x_i, Ratio::new(1, 1) / a_ij);
        for (&col, &val) in row.iter() {
            if col != x_j {
                new_row.insert(col, -val / a_ij);
            }
        }

        for (_basic, other_row) in self.tableau.iter_mut() {
            if let Some(a_ik) = other_row.remove(&x_j) {
                for (&col, &val) in new_row.iter() {
                    let entry = other_row.entry(col).or_insert(Ratio::new(0, 1));
                    *entry += a_ik * val;
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

    pub fn check_feasibility(&mut self) -> bool {
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
                if let Some(lb) = self.lower_bounds.get(&x_i) {
                    if (lb.is_strict && val.le_rational(lb.val)) || (!lb.is_strict && val.lt_rational(lb.val)) {
                        violated_var = Some((x_i, true));
                        break;
                    }
                }
                if let Some(ub) = self.upper_bounds.get(&x_i) {
                    if (ub.is_strict && val.ge_rational(ub.val)) || (!ub.is_strict && val.gt_rational(ub.val)) {
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

                let target_val = if is_lower { 
                    if self.lower_bounds[&x_i].is_strict {
                        DeltaRational::delta_shift(self.lower_bounds[&x_i].val, 1)
                    } else {
                        DeltaRational::rational(self.lower_bounds[&x_i].val)
                    }
                } else if self.upper_bounds[&x_i].is_strict {
                    DeltaRational::delta_shift(self.upper_bounds[&x_i].val, -1)
                } else {
                    DeltaRational::rational(self.upper_bounds[&x_i].val)
                };

                for &x_j in &non_basic_vars {
                    let row = &self.tableau[&x_i];
                    let a_ij = *row.get(&x_j).unwrap_or(&Ratio::new(0, 1));
                    if a_ij == Ratio::new(0, 1) { continue; }
                    
                    let val_j = self.assignment.get(&x_j).cloned().unwrap_or_else(DeltaRational::zero);
                    
                    let can_increase = if let Some(ub) = self.upper_bounds.get(&x_j) {
                        val_j.lt_rational(ub.val)
                    } else { true };
                    let can_decrease = if let Some(lb) = self.lower_bounds.get(&x_j) {
                        val_j.gt_rational(lb.val)
                    } else { true };

                    let a_ij_gt_0 = a_ij > Ratio::new(0, 1);
                    
                    // Comprobar si este pivot mejora la viabilidad
                    let improves = if is_lower {
                        (a_ij_gt_0 && can_increase) || (!a_ij_gt_0 && can_decrease)
                    } else {
                        (a_ij_gt_0 && can_decrease) || (!a_ij_gt_0 && can_increase)
                    };

                    if improves {
                        self.pivot(x_i, x_j);
                        self.update(x_i, target_val);
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
                    for (&var, &coeff) in coeffs {
                        let val = self.assignment.get(&var).cloned().unwrap_or_else(DeltaRational::zero);
                        current_sum = current_sum.add(&val.scale(coeff));
                    }
                    if current_sum == DeltaRational::rational(*target) { violated_idx = Some(idx); break; }
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
        let zero = Ratio::new(0, 1);
        let val_j = self.assignment.get(&x_j).cloned().unwrap_or_else(DeltaRational::zero);
        let mut up: Option<DeltaRational> = self.upper_bounds.get(&x_j)
            .map(|b| DeltaRational { c: b.val - val_j.c, k: -val_j.k });
        let mut down: Option<DeltaRational> = self.lower_bounds.get(&x_j)
            .map(|b| DeltaRational { c: val_j.c - b.val, k: val_j.k });
        for (&x_i, row) in self.tableau.iter() {
            let a_ij = match row.get(&x_j) { Some(&a) if a != zero => a, _ => continue };
            let val_i = self.assignment.get(&x_i).cloned().unwrap_or_else(DeltaRational::zero);
            // Subir x_j por Δ mueve x_i por a_ij*Δ.
            if a_ij > zero {
                if let Some(ub) = self.upper_bounds.get(&x_i) {
                    let room = DeltaRational { c: ub.val - val_i.c, k: -val_i.k }.scale(Ratio::new(1, 1) / a_ij);
                    up = Some(up.map_or(room.clone(), |u| u.min_delta(room)));
                }
                if let Some(lb) = self.lower_bounds.get(&x_i) {
                    let room = DeltaRational { c: val_i.c - lb.val, k: val_i.k }.scale(Ratio::new(1, 1) / a_ij);
                    down = Some(down.map_or(room.clone(), |d| d.min_delta(room)));
                }
            } else {
                let neg = -a_ij;
                if let Some(lb) = self.lower_bounds.get(&x_i) {
                    let room = DeltaRational { c: val_i.c - lb.val, k: val_i.k }.scale(Ratio::new(1, 1) / neg);
                    up = Some(up.map_or(room.clone(), |u| u.min_delta(room)));
                }
                if let Some(ub) = self.upper_bounds.get(&x_i) {
                    let room = DeltaRational { c: ub.val - val_i.c, k: -val_i.k }.scale(Ratio::new(1, 1) / neg);
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
        let zero = Ratio::new(0, 1);
        let one = Ratio::new(1, 1);
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
                let mut r_j = coeffs.get(&x_j).copied().unwrap_or(zero);
                for (&v, &c_v) in &coeffs {
                    if let Some(row) = self.tableau.get(&v) {
                        if let Some(&a_vj) = row.get(&x_j) { r_j += c_v * a_vj; }
                    }
                }
                if r_j != zero {
                    // Cualquier Δ≠0 factible rompe la igualdad (r_j≠0). Paso exacto acotado.
                    let delta = if can_up {
                        match up.clone() {
                            Some(r) if r.c > zero => DeltaRational::rational(r.c.min(one)),
                            Some(r) => DeltaRational { c: zero, k: r.k / Ratio::new(2, 1) },
                            None => DeltaRational::rational(one),
                        }
                    } else if can_down {
                        match down.clone() {
                            Some(r) if r.c > zero => DeltaRational::rational(-(r.c.min(one))),
                            Some(r) => DeltaRational { c: zero, k: -(r.k / Ratio::new(2, 1)) },
                            None => DeltaRational::rational(-one),
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

    fn model_delta(&self) -> Ratio<i64> {
        let zero = Ratio::new(0, 1);
        let mut upper: Option<Ratio<i64>> = None;
        for (&var, value) in &self.assignment {
            if value.k > zero {
                if let Some(ub) = self.upper_bounds.get(&var) {
                    if ub.val > value.c {
                        let limit = (ub.val - value.c) / value.k;
                        upper = Some(upper.map_or(limit, |current| current.min(limit)));
                    }
                }
            } else if value.k < zero {
                if let Some(lb) = self.lower_bounds.get(&var) {
                    if value.c > lb.val {
                        let limit = (value.c - lb.val) / -value.k;
                        upper = Some(upper.map_or(limit, |current| current.min(limit)));
                    }
                }
            }
        }
        match upper {
            Some(limit) if limit > zero => limit / Ratio::new(2, 1),
            _ => Ratio::new(1, 1),
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
                        let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                        let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
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
                val_i.lt_rational(lb.val) || (lb.is_strict && val_i.le_rational(lb.val))
            } else { false };

            if let Some(expr) = self.bound_origins.get(&(x_i, is_lower_violated)) {
                conflict.push(expr.clone());
            }

            if let Some(row) = self.tableau.get(&x_i) {
                for (&x_j, &a_ij) in row.iter() {
                    let a_ij_gt_0 = a_ij > Ratio::new(0, 1);
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
                    let concrete = val.c + val.k * delta;
                    return Some(ModelValue::Real(BigRational::new(BigInt::from(*concrete.numer()), BigInt::from(*concrete.denom())))); // exacto
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
                let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.upper_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            Expr::Lt(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.upper_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: true });
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            Expr::Ge(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.bound_origins.insert((slack, true), origin_expr.clone());
            }
            Expr::Gt(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: true });
                self.bound_origins.insert((slack, true), origin_expr.clone());
            }
            Expr::Eq(lhs, rhs) => {
                let mut coeffs = BTreeMap::new();
                let c1 = self.extract_coeffs(lhs, Ratio::new(1, 1), &mut coeffs);
                let c2 = self.extract_coeffs(rhs, Ratio::new(-1, 1), &mut coeffs);
                let slack = self.create_slack_var();
                self.tableau.insert(slack, coeffs);
                self.basic_vars.push(slack);
                self.lower_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.upper_bounds.insert(slack, Bound { val: -(c1 + c2), is_strict: false });
                self.bound_origins.insert((slack, true), origin_expr.clone());
                self.bound_origins.insert((slack, false), origin_expr.clone());
            }
            _ => {}
        }
    }

    fn extract_coeffs(&mut self, expr: &Expr, scale: Ratio<i64>, coeffs: &mut BTreeMap<usize, Ratio<i64>>) -> Ratio<i64> {
        match expr {
            Expr::Int(i) => scale * Ratio::new(*i, 1),
            Expr::Real(i, s) => scale * Ratio::new(*i, 10i64.pow(*s)),
            Expr::Var(name, _) => {
                let id = self.get_or_create_var(name);
                *coeffs.entry(id).or_insert(Ratio::new(0, 1)) += scale;
                Ratio::new(0, 1)
            }
            Expr::Add(args) => {
                let mut constant = Ratio::new(0, 1);
                for arg in args {
                    constant += self.extract_coeffs(arg, scale, coeffs);
                }
                constant
            }
            Expr::Sub(args) => {
                if args.is_empty() { return Ratio::new(0, 1); }
                let mut constant = self.extract_coeffs(&args[0], scale, coeffs);
                for arg in &args[1..] {
                    constant -= self.extract_coeffs(arg, scale, coeffs);
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
                *coeffs.entry(id).or_insert(Ratio::new(0, 1)) += scale;
                Ratio::new(0, 1)
            }
            _ => {
                let id = self.get_or_create_var(&format!("{}", expr));
                *coeffs.entry(id).or_insert(Ratio::new(0, 1)) += scale;
                Ratio::new(0, 1)
            }
        }
    }

    fn try_eval_const(&self, expr: &Expr) -> Option<Ratio<i64>> {
        match expr {
            Expr::Int(i) => Some(Ratio::new(*i, 1)),
            Expr::Real(i, s) => Some(Ratio::new(*i, 10i64.pow(*s))),
            _ => None,
        }
    }
}
