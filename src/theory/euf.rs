use crate::ast::{Expr, ModelValue};
use crate::theory::TheorySolver;
use std::collections::{BTreeMap, VecDeque};

// REF: [Downey et al., 1980] "Variations on the Common Subexpression Problem"
//      DOI: 10.1145/322203.322228
// REF: [Nelson & Oppen, 1980] "Fast Decision Procedures Based on Congruence Closure"
//      DOI: 10.1145/322217.322220

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Node {
    Var(String),
    App(String, Vec<usize>), 
}

pub struct EufSolver {
    pub(crate) expr_to_id: BTreeMap<Expr, usize>,
    id_to_node: Vec<Node>,
    parent: Vec<usize>,
    /// Proof Forest: (target, reason_expr)
    pub(crate) proof_forest: Vec<Option<(usize, Expr)>>,
    use_list: Vec<Vec<usize>>,
    lookup: BTreeMap<(String, Vec<usize>), usize>,
    disequalities: Vec<(usize, usize, Expr)>,
    /// Cola de fusiones pendientes: (i, j, reason)
    pending: VecDeque<(usize, usize, Option<Expr>)>,
    original_exprs: Vec<Expr>,
    inconsistent: bool,
    conflict: Vec<Expr>,
}

impl Default for EufSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl EufSolver {
    pub fn new() -> Self {
        Self {
            expr_to_id: BTreeMap::new(),
            id_to_node: Vec::new(),
            parent: Vec::new(),
            proof_forest: Vec::new(),
            use_list: Vec::new(),
            lookup: BTreeMap::new(),
            disequalities: Vec::new(),
            pending: VecDeque::new(),
            original_exprs: Vec::new(),
            inconsistent: false,
            conflict: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        self.expr_to_id.clear();
        self.id_to_node.clear();
        self.parent.clear();
        self.proof_forest.clear();
        self.use_list.clear();
        self.lookup.clear();
        self.disequalities.clear();
        self.pending.clear();
        self.original_exprs.clear();
        self.inconsistent = false;
        self.conflict.clear();
    }

    fn find(&mut self, i: usize) -> usize {
        if self.parent[i] == i {
            i
        } else {
            self.parent[i] = self.find(self.parent[i]);
            self.parent[i]
        }
    }

    fn get_id(&mut self, expr: &Expr) -> usize {
        if let Some(&id) = self.expr_to_id.get(expr) {
            return id;
        }

        let id = self.id_to_node.len();
        let node = match expr {
            Expr::Var(name, _) => Node::Var(name.clone()),
            Expr::App(name, args) => {
                let mut arg_ids = Vec::new();
                for arg in args {
                    arg_ids.push(self.get_id(arg));
                }
                for &arg_id in &arg_ids {
                    while self.use_list.len() <= arg_id { self.use_list.push(Vec::new()); }
                    self.use_list[arg_id].push(id);
                }
                Node::App(name.clone(), arg_ids)
            }
            _ => Node::Var(format!("{:?}", expr)),
        };

        self.expr_to_id.insert(expr.clone(), id);
        self.id_to_node.push(node);
        self.parent.push(id);
        self.proof_forest.push(None);
        while self.use_list.len() <= id { self.use_list.push(Vec::new()); }
        self.original_exprs.push(expr.clone());
        id
    }

    fn merge(&mut self, i: usize, j: usize, reason: Option<Expr>) {
        let root_i = self.find(i);
        let root_j = self.find(j);
        if root_i != root_j {
            self.pending.push_back((root_i, root_j, reason));
        }
    }

    fn process_pending(&mut self) {
        while let Some((root_i, root_j, reason)) = self.pending.pop_front() {
            let actual_root_i = self.find(root_i);
            let actual_root_j = self.find(root_j);
            if actual_root_i == actual_root_j { continue; }

            let parents_i = self.use_list[actual_root_i].clone();
            
            // Unir en Union-Find
            self.parent[actual_root_i] = actual_root_j;
            if let Some(r) = reason {
                self.proof_forest[actual_root_i] = Some((actual_root_j, r));
            }
            
            // Actualizar la Use List del nuevo raíz
            let mut p_i = parents_i;
            self.use_list[actual_root_j].append(&mut p_i);

            // Verificar congruencia solo en los padres afectados
            let affected: Vec<usize> = self.use_list[actual_root_j].clone();
            for p_id in affected {
                if let Node::App(name, args) = self.id_to_node[p_id].clone() {
                    let mut canon_args = Vec::new();
                    for &arg_id in &args {
                        canon_args.push(self.find(arg_id));
                    }
                    let key = (name, canon_args);
                    
                    if let Some(&other_p_id) = self.lookup.get(&key) {
                        if self.find(p_id) != self.find(other_p_id) {
                            self.merge(p_id, other_p_id, None);
                        }
                    } else {
                        self.lookup.insert(key, p_id);
                    }
                }
            }
        }
    }

    pub fn get_expr(&self, id: usize) -> &Expr { &self.original_exprs[id] }
    pub fn get_node(&self, id: usize) -> &Node { &self.id_to_node[id] }
    pub fn find_public(&mut self, i: usize) -> usize { self.find(i) }
    pub fn get_id_public(&self, expr: &Expr) -> Option<usize> { self.expr_to_id.get(expr).copied() }
    pub fn get_num_ids(&self) -> usize { self.parent.len() }
    pub fn get_classes(&mut self) -> BTreeMap<usize, Vec<usize>> {
        let mut classes = BTreeMap::new();
        let n = self.parent.len();
        for i in 0..n {
            let root = self.find(i);
            classes.entry(root).or_insert(Vec::new()).push(i);
        }
        classes
    }
}

impl TheorySolver for EufSolver {
    fn assert(&mut self, expr: &Expr) {
        if self.inconsistent { return; }
        match expr {
            Expr::Eq(a, b) => {
                let id_a = self.get_id(a);
                let id_b = self.get_id(b);
                self.merge(id_a, id_b, Some(expr.clone()));
            }
            Expr::Not(inner) => {
                if let Expr::Eq(a, b) = &**inner {
                    let id_a = self.get_id(a);
                    let id_b = self.get_id(b);
                    self.disequalities.push((id_a, id_b, expr.clone()));
                }
            }
            _ => {}
        }
    }

    fn check(&mut self) -> bool {
        if self.inconsistent { return false; }
        self.process_pending();
        let diseqs = self.disequalities.clone();
        for (d1, d2, expr) in diseqs {
            if self.find(d1) == self.find(d2) {
                self.inconsistent = true;
                self.conflict = vec![expr.clone()];
                return false;
            }
        }
        true
    }

    fn explain(&self) -> Vec<Expr> { self.conflict.clone() }

    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> {
        None
    }
}
