pub mod lra;
pub mod euf;
pub mod bv;
pub mod array;
pub mod quantifier;
pub mod string;
pub mod nla;
pub mod fp;

pub use lra::LraSolver;
pub use euf::EufSolver;
pub use bv::BitBlaster;
pub use array::ArraySolver;
pub use quantifier::QuantifierSolver;
pub use string::StringSolver;
pub use nla::NlaSolver;
pub use crate::ast::fp::{FloatSort, FloatValue, RoundingMode};

use crate::ast::{Expr, ModelValue};

/// Interfaz fundamental para Solvers de Teoría (Theory Solvers).
/// Permite al núcleo SAT delegar la verificación de restricciones no booleanas.
pub trait TheorySolver {
    /// Añade una restricción a la teoría actual.
    fn assert(&mut self, expr: &Expr);
    /// Verifica si el conjunto actual de restricciones es consistente (Satisfiable).
    fn check(&mut self) -> bool;
    /// En caso de conflicto (Unsat), devuelve el subconjunto de expresiones que lo causan.
    fn explain(&self) -> Vec<Expr>;
    /// Obtiene el valor asignado a una expresión en el modelo actual.
    fn get_model_value(&self, expr: &Expr) -> Option<ModelValue>;
}

#[derive(Debug, Clone)]
pub struct Bound {
    pub val: f64,
    pub is_strict: bool,
}
