pub mod array;
pub mod bv;
pub mod euf;
pub mod fp;
pub mod lra;
pub mod nla;
pub mod quantifier;
pub mod string;

pub use crate::ast::fp::{FloatSort, FloatValue, RoundingMode};
pub use array::ArraySolver;
pub use bv::BitBlaster;
pub use euf::EufSolver;
pub use lra::LraSolver;
pub use nla::NlaSolver;
pub use quantifier::QuantifierSolver;
pub use string::StringSolver;

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
    pub val: num_rational::BigRational,
    pub is_strict: bool,
}
