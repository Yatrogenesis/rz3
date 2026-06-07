use crate::ast::{Expr, ModelValue};
use crate::theory::TheorySolver;
use std::collections::{BTreeSet, BTreeMap};

pub struct StringSolver {
    /// Lemas de longitud ya instanciados
    instantiated_axioms: BTreeSet<Expr>,
    /// Nuevos lemas encontrados en esta pasada
    pending_lemmas: Vec<Expr>,
}

impl Default for StringSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl StringSolver {
    pub fn new() -> Self {
        Self {
            instantiated_axioms: BTreeSet::new(),
            pending_lemmas: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        self.pending_lemmas.clear();
    }

    fn collect_terms(&mut self, expr: &Expr) {
        match expr {
            Expr::StrLen(s) => {
                // Recolectar SIEMPRE; el dedup se hace al EMITIR (generate_lemmas),
                // no aquí. Si se dedup aquí, el assert inicial (assert_no_track ->
                // string.assert) pre-instancia el axioma y el loop nunca lo emite al SAT.
                let axiom = Expr::Ge(Box::new(Expr::StrLen(s.clone())), Box::new(Expr::Int(0)));
                self.pending_lemmas.push(axiom);
                self.collect_terms(s);
            }
            Expr::StrConst(s) => {
                let axiom = Expr::Eq(Box::new(Expr::StrLen(Box::new(expr.clone()))), Box::new(Expr::Int(s.len() as i64)));
                self.pending_lemmas.push(axiom);
            }
            Expr::StrConcat(args) => {
                for arg in args { self.collect_terms(arg); }
            }
            Expr::StrContains(a, b) => {
                self.collect_terms(a);
                self.collect_terms(b);
            }
            Expr::Eq(a, b) | Expr::Lt(a, b) | Expr::Le(a, b) | Expr::Gt(a, b) | Expr::Ge(a, b) => {
                self.collect_terms(a);
                self.collect_terms(b);
            }
            Expr::Not(inner) => self.collect_terms(inner),
            Expr::And(args) | Expr::Or(args) | Expr::Add(args) | Expr::Sub(args) | Expr::Mul(args) => {
                for arg in args { self.collect_terms(arg); }
            }
            _ => {}
        }
    }

    pub fn generate_lemmas(&mut self) -> Vec<Expr> {
        // Dedup en el momento de EMISIÓN: solo lemas aún no enviados al SAT core.
        // Evita re-emitir (loop infinito) y permite emitir los recolectados en este round.
        let mut out = Vec::new();
        for axiom in std::mem::take(&mut self.pending_lemmas) {
            if self.instantiated_axioms.insert(axiom.clone()) {
                out.push(axiom);
            }
        }
        out
    }
}

impl TheorySolver for StringSolver {
    fn assert(&mut self, expr: &Expr) {
        self.collect_terms(expr);
    }

    fn check(&mut self) -> bool {
        // Implementación básica: verificar que no haya contradicciones en longitudes
        // Ej: (str.len s) = 3 y (str.len s) = 5
        let mut lengths: BTreeMap<Expr, i64> = BTreeMap::new();
        
        for lemma in &self.pending_lemmas {
            if let Expr::Eq(a, b) = lemma {
                if let (Expr::StrLen(s), Expr::Int(len)) = (&**a, &**b) {
                    if let Some(&prev_len) = lengths.get(s) {
                        if prev_len != *len {
                            return false; // Conflicto
                        }
                    } else {
                        lengths.insert(*s.clone(), *len);
                    }
                }
            }
        }
        true
    }

    fn explain(&self) -> Vec<Expr> {
        Vec::new()
    }

    fn get_model_value(&self, _expr: &Expr) -> Option<ModelValue> {
        None
    }
}
