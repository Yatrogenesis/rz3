use crate::ast::{Expr, ModelValue};
use crate::theory::TheorySolver;
use std::collections::BTreeSet;

pub struct ArraySolver {
    /// Conjunto de axiomas de instanciación (Select sobre Store)
    instantiated_axioms: BTreeSet<Expr>,
    /// Expresiones de array presentes en el modelo actual
    arrays: BTreeSet<Expr>,
    /// Consultas de lectura (select) realizadas
    reads: BTreeSet<Expr>,
}

impl Default for ArraySolver {
    fn default() -> Self {
        Self::new()
    }
}

impl ArraySolver {
    pub fn new() -> Self {
        Self {
            instantiated_axioms: BTreeSet::new(),
            arrays: BTreeSet::new(),
            reads: BTreeSet::new(),
        }
    }

    pub fn reset(&mut self) {
        self.arrays.clear();
        self.reads.clear();
    }

    /// Recolecta todos los términos Select y Store para instanciar axiomas.
    fn collect_terms(&mut self, expr: &Expr) {
        match expr {
            Expr::Select(a, i) => {
                self.reads.insert(expr.clone());
                self.collect_terms(a);
                self.collect_terms(i);
            }
            Expr::Store(a, i, v) => {
                self.arrays.insert(expr.clone());
                self.collect_terms(a);
                self.collect_terms(i);
                self.collect_terms(v);
            }
            Expr::Eq(a, b) => {
                self.collect_terms(a);
                self.collect_terms(b);
            }
            Expr::Not(inner) => self.collect_terms(inner),
            Expr::And(args) | Expr::Or(args) | Expr::Add(args) => {
                for arg in args {
                    self.collect_terms(arg);
                }
            }
            _ => {}
        }
    }
}

impl TheorySolver for ArraySolver {
    fn assert(&mut self, expr: &Expr) {
        self.collect_terms(expr);
    }

    fn check(&mut self) -> bool {
        true
    }

    fn explain(&self) -> Vec<Expr> {
        Vec::new()
    }

    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> {
        None
    }
}

impl ArraySolver {
    /// Genera nuevos lemas basados en los axiomas de la teoría de arreglos.
    /// Estos lemas se añaden al SAT solver para refinar el modelo.
    pub fn generate_lemmas(&mut self) -> Vec<Expr> {
        let mut lemmas = Vec::new();

        // Axioma 1: (select (store a i v) i) = v
        for arr_expr in &self.arrays {
            if let Expr::Store(_a, i, v) = arr_expr {
                let select_store = Expr::Select(Box::new(arr_expr.clone()), i.clone());
                let axiom = Expr::Eq(Box::new(select_store), v.clone());
                if self.instantiated_axioms.insert(axiom.clone()) {
                    lemmas.push(axiom);
                }
            }
        }

        // Axioma 2: i != j => (select (store a i v) j) = (select a j)
        // Solo instanciamos si ya existe un select sobre el store con un índice distinto
        for read_expr in &self.reads {
            if let Expr::Select(arr_ptr, j) = read_expr {
                if let Expr::Store(a, i, _v) = &**arr_ptr {
                    // Axioma: (i = j) OR (select (store a i v) j) = (select a j)
                    let i_eq_j = Expr::Eq(i.clone(), j.clone());
                    let select_a_j = Expr::Select(a.clone(), j.clone());
                    let select_store_j = Expr::Select(arr_ptr.clone(), j.clone());
                    let s_eq_s = Expr::Eq(Box::new(select_store_j), Box::new(select_a_j));

                    let lemma = Expr::Or(vec![i_eq_j, s_eq_s]);
                    if self.instantiated_axioms.insert(lemma.clone()) {
                        lemmas.push(lemma);
                    }
                }
            }
        }

        lemmas
    }
}
