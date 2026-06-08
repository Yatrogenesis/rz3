//! Tipos canónicos de punto flotante IEEE-754 para valores de modelo.
//!
//! Viven en `ast` (capa baja) para que `theory::fp` los consuma SIN invertir
//! capas (ast NO debe depender de theory). `ModelValue::Float` usa `FloatValue`.
//! Estos tipos son el CONTRATO compartido: `theory::fp` debe `use crate::ast::fp::*`
//! en vez de definirlos localmente. [coordinación Claude/codex 2026-06-08]

use num_bigint::BigUint;
use num_rational::BigRational;

/// Modos de redondeo IEEE-754.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RoundingMode {
    NearestTiesToEven,
    TowardZero,
    TowardPositive,
    TowardNegative,
}

/// Formato del float: anchura de exponente y de significando.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FloatSort {
    pub exponent_bits: u16,
    pub significand_bits: u16,
}

/// Clase de valor IEEE-754 con representación EXACTA (sin f64/aproximación).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FloatClass {
    QuietNaN { payload: BigUint },
    PositiveInfinity,
    NegativeInfinity,
    PositiveZero,
    NegativeZero,
    Finite { negative: bool, value: BigRational },
}

/// Valor de modelo FP completo: formato + clase.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FloatValue {
    pub sort: FloatSort,
    pub class: FloatClass,
}
