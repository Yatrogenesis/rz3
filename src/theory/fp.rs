use crate::ast::fp::{FloatClass, FloatSort, FloatValue, RoundingMode};
use crate::ast::{Expr, ModelValue};
use crate::theory::TheorySolver;
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

// REF: IEEE Std 754-2019 "IEEE Standard for Floating-Point Arithmetic"
//      ISBN: 978-1-5044-5925-8
//      Validado contra: patrones binarios IEEE binary16/binary32/binary64 y reglas
//      roundTiesToEven, roundTowardZero, roundTowardPositive, roundTowardNegative.

impl FloatSort {
    pub const BINARY16: Self = Self {
        exponent_bits: 5,
        significand_bits: 11,
    };
    pub const BINARY32: Self = Self {
        exponent_bits: 8,
        significand_bits: 24,
    };
    pub const BINARY64: Self = Self {
        exponent_bits: 11,
        significand_bits: 53,
    };

    pub fn new(exponent_bits: u16, significand_bits: u16) -> Option<Self> {
        if exponent_bits < 2
            || significand_bits < 2
            || exponent_bits >= 63
            || significand_bits >= 1024
        {
            None
        } else {
            Some(Self {
                exponent_bits,
                significand_bits,
            })
        }
    }

    fn exponent_max(self) -> u64 {
        (1u64 << self.exponent_bits) - 1
    }

    fn exponent_bias(self) -> i64 {
        (1i64 << (self.exponent_bits - 1)) - 1
    }

    fn fraction_bits(self) -> u16 {
        self.significand_bits - 1
    }
}

impl FloatValue {
    pub fn from_bits(sort: FloatSort, bits: &BigUint) -> Option<Self> {
        let sign_bit = bit_at(bits, (sort.exponent_bits + sort.fraction_bits()) as usize);
        let exponent = extract_u64(
            bits,
            sort.fraction_bits() as usize,
            sort.exponent_bits as usize,
        )?;
        let fraction = extract_biguint(bits, 0, sort.fraction_bits() as usize);
        let class = decode_fields(sort, sign_bit, exponent, &fraction)?;
        Some(Self { sort, class })
    }

    pub fn to_bits(&self, mode: RoundingMode) -> BigUint {
        encode_value(self.sort, &self.class, mode)
    }

    pub fn add(&self, other: &Self, mode: RoundingMode) -> Option<Self> {
        same_sort(self, other)?;
        let class = match (&self.class, &other.class) {
            (FloatClass::QuietNaN { payload }, _) | (_, FloatClass::QuietNaN { payload }) => {
                FloatClass::QuietNaN {
                    payload: payload.clone(),
                }
            }
            (FloatClass::PositiveInfinity, FloatClass::NegativeInfinity)
            | (FloatClass::NegativeInfinity, FloatClass::PositiveInfinity) => {
                default_nan(self.sort)
            }
            (FloatClass::PositiveInfinity, _) | (_, FloatClass::PositiveInfinity) => {
                FloatClass::PositiveInfinity
            }
            (FloatClass::NegativeInfinity, _) | (_, FloatClass::NegativeInfinity) => {
                FloatClass::NegativeInfinity
            }
            _ => {
                let sum = self.exact_rational()? + other.exact_rational()?;
                class_from_rounded_bits(self.sort, &sum, mode)
            }
        };
        Some(Self {
            sort: self.sort,
            class,
        })
    }

    pub fn sub(&self, other: &Self, mode: RoundingMode) -> Option<Self> {
        self.add(&other.neg(), mode)
    }

    pub fn mul(&self, other: &Self, mode: RoundingMode) -> Option<Self> {
        same_sort(self, other)?;
        let class = match (&self.class, &other.class) {
            (FloatClass::QuietNaN { payload }, _) | (_, FloatClass::QuietNaN { payload }) => {
                FloatClass::QuietNaN {
                    payload: payload.clone(),
                }
            }
            (a, b) if is_zero(a) && is_infinite(b) || is_infinite(a) && is_zero(b) => {
                default_nan(self.sort)
            }
            (a, b) if is_infinite(a) || is_infinite(b) => {
                if sign_negative(a) ^ sign_negative(b) {
                    FloatClass::NegativeInfinity
                } else {
                    FloatClass::PositiveInfinity
                }
            }
            _ => {
                let product = self.exact_rational()? * other.exact_rational()?;
                class_from_rounded_bits(self.sort, &product, mode)
            }
        };
        Some(Self {
            sort: self.sort,
            class,
        })
    }

    pub fn div(&self, other: &Self, mode: RoundingMode) -> Option<Self> {
        same_sort(self, other)?;
        let class = match (&self.class, &other.class) {
            (FloatClass::QuietNaN { payload }, _) | (_, FloatClass::QuietNaN { payload }) => {
                FloatClass::QuietNaN {
                    payload: payload.clone(),
                }
            }
            (a, b) if is_zero(a) && is_zero(b) => default_nan(self.sort),
            (a, b) if is_infinite(a) && is_infinite(b) => default_nan(self.sort),
            (a, b) if is_infinite(a) => {
                if sign_negative(a) ^ sign_negative(b) {
                    FloatClass::NegativeInfinity
                } else {
                    FloatClass::PositiveInfinity
                }
            }
            (a, b) if is_infinite(b) => {
                if sign_negative(a) ^ sign_negative(b) {
                    FloatClass::NegativeZero
                } else {
                    FloatClass::PositiveZero
                }
            }
            (a, b) if is_zero(b) => {
                if sign_negative(a) ^ sign_negative(b) {
                    FloatClass::NegativeInfinity
                } else {
                    FloatClass::PositiveInfinity
                }
            }
            _ => {
                let quotient = self.exact_rational()? / other.exact_rational()?;
                class_from_rounded_bits(self.sort, &quotient, mode)
            }
        };
        Some(Self {
            sort: self.sort,
            class,
        })
    }

    pub fn sqrt(&self, mode: RoundingMode) -> Option<Self> {
        let class = match &self.class {
            FloatClass::QuietNaN { payload } => FloatClass::QuietNaN {
                payload: payload.clone(),
            },
            FloatClass::NegativeInfinity => default_nan(self.sort),
            FloatClass::PositiveInfinity => FloatClass::PositiveInfinity,
            FloatClass::NegativeZero => FloatClass::NegativeZero,
            FloatClass::PositiveZero => FloatClass::PositiveZero,
            FloatClass::Finite { negative: true, .. } => default_nan(self.sort),
            FloatClass::Finite { value, .. } => {
                let rounded = sqrt_round_to_float_bits(self.sort, value, mode)?;
                decode_to_class(self.sort, &rounded)?
            }
        };
        Some(Self {
            sort: self.sort,
            class,
        })
    }

    pub fn neg(&self) -> Self {
        let class = match &self.class {
            FloatClass::QuietNaN { payload } => FloatClass::QuietNaN {
                payload: payload.clone(),
            },
            FloatClass::PositiveInfinity => FloatClass::NegativeInfinity,
            FloatClass::NegativeInfinity => FloatClass::PositiveInfinity,
            FloatClass::PositiveZero => FloatClass::NegativeZero,
            FloatClass::NegativeZero => FloatClass::PositiveZero,
            FloatClass::Finite { negative, value } => FloatClass::Finite {
                negative: !negative,
                value: value.clone(),
            },
        };
        Self {
            sort: self.sort,
            class,
        }
    }

    pub fn abs(&self) -> Self {
        let class = match &self.class {
            FloatClass::QuietNaN { payload } => FloatClass::QuietNaN {
                payload: payload.clone(),
            },
            FloatClass::PositiveInfinity | FloatClass::NegativeInfinity => {
                FloatClass::PositiveInfinity
            }
            FloatClass::PositiveZero | FloatClass::NegativeZero => FloatClass::PositiveZero,
            FloatClass::Finite { value, .. } => FloatClass::Finite {
                negative: false,
                value: value.clone(),
            },
        };
        Self {
            sort: self.sort,
            class,
        }
    }

    fn exact_rational(&self) -> Option<BigRational> {
        match &self.class {
            FloatClass::PositiveZero | FloatClass::NegativeZero => Some(BigRational::zero()),
            FloatClass::Finite { negative, value } => {
                if *negative {
                    Some(-value.clone())
                } else {
                    Some(value.clone())
                }
            }
            _ => None,
        }
    }
}

fn same_sort(a: &FloatValue, b: &FloatValue) -> Option<()> {
    if a.sort == b.sort {
        Some(())
    } else {
        None
    }
}

fn decode_fields(
    sort: FloatSort,
    sign: bool,
    exponent: u64,
    fraction: &BigUint,
) -> Option<FloatClass> {
    if exponent == sort.exponent_max() {
        return Some(if fraction.is_zero() {
            if sign {
                FloatClass::NegativeInfinity
            } else {
                FloatClass::PositiveInfinity
            }
        } else {
            FloatClass::QuietNaN {
                payload: fraction.clone(),
            }
        });
    }

    if exponent == 0 && fraction.is_zero() {
        return Some(if sign {
            FloatClass::NegativeZero
        } else {
            FloatClass::PositiveZero
        });
    }

    let frac_den = pow2_biguint(sort.fraction_bits() as usize);
    let significand = if exponent == 0 {
        BigRational::new(biguint_to_bigint(fraction), biguint_to_bigint(&frac_den))
    } else {
        BigRational::new(
            biguint_to_bigint(&(pow2_biguint(sort.fraction_bits() as usize) + fraction)),
            biguint_to_bigint(&frac_den),
        )
    };
    let e = if exponent == 0 {
        1 - sort.exponent_bias()
    } else {
        exponent as i64 - sort.exponent_bias()
    };
    let value = significand * pow2_ratio(e);
    Some(FloatClass::Finite {
        negative: sign,
        value,
    })
}

fn encode_value(sort: FloatSort, class: &FloatClass, mode: RoundingMode) -> BigUint {
    match class {
        FloatClass::QuietNaN { payload } => compose_bits(sort, false, sort.exponent_max(), payload),
        FloatClass::PositiveInfinity => {
            compose_bits(sort, false, sort.exponent_max(), &BigUint::zero())
        }
        FloatClass::NegativeInfinity => {
            compose_bits(sort, true, sort.exponent_max(), &BigUint::zero())
        }
        FloatClass::PositiveZero => compose_bits(sort, false, 0, &BigUint::zero()),
        FloatClass::NegativeZero => compose_bits(sort, true, 0, &BigUint::zero()),
        FloatClass::Finite { negative, value } => {
            round_finite_to_bits(sort, *negative, value, mode)
        }
    }
}

fn class_from_rounded_bits(sort: FloatSort, value: &BigRational, mode: RoundingMode) -> FloatClass {
    decode_to_class(sort, &round_signed_rational_to_bits(sort, value, mode))
        .unwrap_or_else(|| default_nan(sort))
}

fn decode_to_class(sort: FloatSort, bits: &BigUint) -> Option<FloatClass> {
    FloatValue::from_bits(sort, bits).map(|v| v.class)
}

fn round_signed_rational_to_bits(
    sort: FloatSort,
    value: &BigRational,
    mode: RoundingMode,
) -> BigUint {
    if value.is_zero() {
        return compose_bits(sort, value.is_negative(), 0, &BigUint::zero());
    }
    let negative = value.is_negative();
    round_finite_to_bits(sort, negative, &value.abs(), mode)
}

fn round_finite_to_bits(
    sort: FloatSort,
    negative: bool,
    magnitude: &BigRational,
    mode: RoundingMode,
) -> BigUint {
    if magnitude.is_zero() {
        return compose_bits(sort, negative, 0, &BigUint::zero());
    }

    let min_normal_exp = 1 - sort.exponent_bias();
    let max_normal_exp = sort.exponent_max() as i64 - 1 - sort.exponent_bias();
    let mut exponent = floor_log2_rational(magnitude);

    if exponent > max_normal_exp {
        return overflow_bits(sort, negative, mode);
    }

    if exponent >= min_normal_exp {
        let scaled = magnitude / pow2_ratio(exponent - sort.fraction_bits() as i64);
        let rounded = round_integer(&scaled, negative, mode);
        let limit = BigInt::one() << sort.significand_bits;
        let mut significand = rounded;
        if significand >= limit {
            significand >>= 1usize;
            exponent += 1;
            if exponent > max_normal_exp {
                return overflow_bits(sort, negative, mode);
            }
        }
        let biased = (exponent + sort.exponent_bias()) as u64;
        let hidden = BigInt::one() << sort.fraction_bits();
        let fraction = bigint_to_biguint(&(significand - hidden)).unwrap_or_default();
        compose_bits(sort, negative, biased, &fraction)
    } else {
        let scaled = magnitude / pow2_ratio(min_normal_exp - sort.fraction_bits() as i64);
        let significand = round_integer(&scaled, negative, mode);
        if significand.is_zero() {
            return compose_bits(sort, negative, 0, &BigUint::zero());
        }
        let normal_threshold = BigInt::one() << sort.fraction_bits();
        if significand >= normal_threshold {
            compose_bits(sort, negative, 1, &BigUint::zero())
        } else {
            compose_bits(
                sort,
                negative,
                0,
                &bigint_to_biguint(&significand).unwrap_or_default(),
            )
        }
    }
}

fn overflow_bits(sort: FloatSort, negative: bool, mode: RoundingMode) -> BigUint {
    match (negative, mode) {
        (false, RoundingMode::TowardZero | RoundingMode::TowardNegative) => {
            max_finite_bits(sort, false)
        }
        (true, RoundingMode::TowardZero | RoundingMode::TowardPositive) => {
            max_finite_bits(sort, true)
        }
        _ => compose_bits(sort, negative, sort.exponent_max(), &BigUint::zero()),
    }
}

fn max_finite_bits(sort: FloatSort, negative: bool) -> BigUint {
    let fraction = pow2_biguint(sort.fraction_bits() as usize) - BigUint::one();
    compose_bits(sort, negative, sort.exponent_max() - 1, &fraction)
}

fn round_integer(value: &BigRational, negative: bool, mode: RoundingMode) -> BigInt {
    let n = value.numer();
    let d = value.denom();
    let q = n / d;
    let r = n % d;
    if r.is_zero() {
        return q;
    }

    match mode {
        RoundingMode::TowardZero => q,
        RoundingMode::TowardPositive => {
            if negative {
                q
            } else {
                q + 1
            }
        }
        RoundingMode::TowardNegative => {
            if negative {
                q + 1
            } else {
                q
            }
        }
        RoundingMode::NearestTiesToEven => {
            let twice_r = r << 1usize;
            if twice_r < *d {
                q
            } else if twice_r > *d {
                q + 1
            } else if (&q & BigInt::one()).is_zero() {
                q
            } else {
                q + 1
            }
        }
    }
}

fn sqrt_round_to_float_bits(
    sort: FloatSort,
    value: &BigRational,
    mode: RoundingMode,
) -> Option<BigUint> {
    if value.is_negative() {
        return None;
    }
    let negative = false;
    if value.is_zero() {
        return Some(compose_bits(sort, false, 0, &BigUint::zero()));
    }

    let min_normal_exp = 1 - sort.exponent_bias();
    let max_normal_exp = sort.exponent_max() as i64 - 1 - sort.exponent_bias();
    let mut exponent = floor_log2_sqrt_rational(value);
    if exponent > max_normal_exp {
        return Some(overflow_bits(sort, false, mode));
    }

    if exponent < min_normal_exp {
        let shift = 2 * (sort.fraction_bits() as i64 - min_normal_exp);
        let scaled = value * pow2_ratio(shift);
        let significand = round_sqrt_integer(&scaled, negative, mode)?;
        if significand.is_zero() {
            return Some(compose_bits(sort, false, 0, &BigUint::zero()));
        }
        let normal_threshold = BigInt::one() << sort.fraction_bits();
        if significand >= normal_threshold {
            return Some(compose_bits(sort, false, 1, &BigUint::zero()));
        }
        return Some(compose_bits(
            sort,
            false,
            0,
            &bigint_to_biguint(&significand).unwrap_or_default(),
        ));
    }

    let shift = 2 * (sort.fraction_bits() as i64 - exponent);
    let scaled = value * pow2_ratio(shift);
    let mut significand = round_sqrt_integer(&scaled, negative, mode)?;
    let limit = BigInt::one() << sort.significand_bits;
    if significand >= limit {
        significand >>= 1usize;
        exponent += 1;
        if exponent > max_normal_exp {
            return Some(overflow_bits(sort, false, mode));
        }
    }
    let hidden = BigInt::one() << sort.fraction_bits();
    let fraction = bigint_to_biguint(&(significand - hidden)).unwrap_or_default();
    Some(compose_bits(
        sort,
        false,
        (exponent + sort.exponent_bias()) as u64,
        &fraction,
    ))
}

fn round_sqrt_integer(value: &BigRational, negative: bool, mode: RoundingMode) -> Option<BigInt> {
    let n = value.numer();
    let d = value.denom();
    let mut lo = BigInt::zero();
    let mut hi = sqrt_upper_bound(n) + 1;
    while lo < hi {
        let mid = (&lo + &hi + 1) >> 1usize;
        if &mid * &mid * d <= *n {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    let floor = lo;
    let floor_sq = &floor * &floor * d;
    if floor_sq == *n {
        return Some(floor);
    }
    match mode {
        RoundingMode::TowardZero | RoundingMode::TowardNegative if !negative => Some(floor),
        RoundingMode::TowardPositive if !negative => Some(floor + 1),
        RoundingMode::TowardZero | RoundingMode::TowardPositive => Some(floor),
        RoundingMode::TowardNegative => Some(floor + 1),
        RoundingMode::NearestTiesToEven => {
            let ceil = &floor + 1;
            let lower_dist = n - floor_sq;
            let upper_dist = &ceil * &ceil * d - n;
            if lower_dist < upper_dist {
                Some(floor)
            } else if lower_dist > upper_dist {
                Some(ceil)
            } else if (&floor & BigInt::one()).is_zero() {
                Some(floor)
            } else {
                Some(ceil)
            }
        }
    }
}

fn floor_log2_rational(value: &BigRational) -> i64 {
    let n_bits = value.numer().bits() as i64;
    let d_bits = value.denom().bits() as i64;
    let mut e = n_bits - d_bits;
    while value < &pow2_ratio(e) {
        e -= 1;
    }
    while value >= &pow2_ratio(e + 1) {
        e += 1;
    }
    e
}

fn floor_log2_sqrt_rational(value: &BigRational) -> i64 {
    let e = floor_log2_rational(value);
    e.div_euclid(2)
}

fn sqrt_upper_bound(value: &BigInt) -> BigInt {
    if value.is_zero() {
        BigInt::zero()
    } else {
        BigInt::one() << ((value.bits() + 1) / 2)
    }
}

fn compose_bits(sort: FloatSort, negative: bool, exponent: u64, fraction: &BigUint) -> BigUint {
    let mut bits = BigUint::from(exponent) << sort.fraction_bits();
    bits |= fraction;
    if negative {
        bits |= BigUint::one() << (sort.exponent_bits + sort.fraction_bits());
    }
    bits
}

fn bit_at(bits: &BigUint, index: usize) -> bool {
    ((bits >> index) & BigUint::one()) == BigUint::one()
}

fn extract_u64(bits: &BigUint, offset: usize, width: usize) -> Option<u64> {
    extract_biguint(bits, offset, width).to_u64()
}

fn extract_biguint(bits: &BigUint, offset: usize, width: usize) -> BigUint {
    let mask = (BigUint::one() << width) - BigUint::one();
    (bits >> offset) & mask
}

fn pow2_biguint(bits: usize) -> BigUint {
    BigUint::one() << bits
}

fn pow2_ratio(exp: i64) -> BigRational {
    if exp >= 0 {
        BigRational::from_integer(BigInt::one() << exp as usize)
    } else {
        BigRational::new(BigInt::one(), BigInt::one() << (-exp) as usize)
    }
}

fn biguint_to_bigint(value: &BigUint) -> BigInt {
    BigInt::from_biguint(Sign::Plus, value.clone())
}

fn bigint_to_biguint(value: &BigInt) -> Option<BigUint> {
    value.to_biguint()
}

fn default_nan(sort: FloatSort) -> FloatClass {
    let quiet_bit = BigUint::one() << (sort.fraction_bits() - 1);
    FloatClass::QuietNaN { payload: quiet_bit }
}

fn is_zero(class: &FloatClass) -> bool {
    matches!(class, FloatClass::PositiveZero | FloatClass::NegativeZero)
}

fn is_infinite(class: &FloatClass) -> bool {
    matches!(
        class,
        FloatClass::PositiveInfinity | FloatClass::NegativeInfinity
    )
}

fn sign_negative(class: &FloatClass) -> bool {
    match class {
        FloatClass::NegativeInfinity | FloatClass::NegativeZero => true,
        FloatClass::Finite { negative, .. } => *negative,
        _ => false,
    }
}

#[derive(Default)]
pub struct FpSolver {
    assertions: Vec<Expr>,
    conflict: Vec<Expr>,
}

impl FpSolver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reset(&mut self) {
        self.assertions.clear();
        self.conflict.clear();
    }

    fn eval_bool(&self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Bool(b) => Some(*b),
            Expr::Not(inner) => self.eval_bool(inner).map(|b| !b),
            Expr::And(args) => {
                let mut out = true;
                for arg in args {
                    out &= self.eval_bool(arg)?;
                }
                Some(out)
            }
            Expr::Or(args) => {
                let mut out = false;
                for arg in args {
                    out |= self.eval_bool(arg)?;
                }
                Some(out)
            }
            Expr::Implies(a, b) => Some(!self.eval_bool(a)? || self.eval_bool(b)?),
            Expr::Eq(a, b) => Some(self.fp_eq(&self.eval_fp(a)?, &self.eval_fp(b)?)),
            Expr::App(name, args) if name == "fp.isNaN" => Some(matches!(
                self.eval_fp(args.first()?)?.class,
                FloatClass::QuietNaN { .. }
            )),
            Expr::App(name, args) if name == "fp.isInfinite" => Some(matches!(
                self.eval_fp(args.first()?)?.class,
                FloatClass::PositiveInfinity | FloatClass::NegativeInfinity
            )),
            Expr::App(name, args) if name == "fp.isZero" => {
                match self.eval_fp(args.first()?)?.class {
                    FloatClass::PositiveZero | FloatClass::NegativeZero => Some(true),
                    FloatClass::Finite { value, .. } => Some(value.is_zero()),
                    _ => Some(false),
                }
            }
            Expr::App(name, args) if name == "fp.isPositive" => {
                match self.eval_fp(args.first()?)?.class {
                    FloatClass::PositiveInfinity | FloatClass::PositiveZero => Some(true),
                    FloatClass::Finite { negative, .. } => Some(!negative),
                    _ => Some(false),
                }
            }
            Expr::App(name, args) if name == "fp.isNegative" => {
                match self.eval_fp(args.first()?)?.class {
                    FloatClass::NegativeInfinity | FloatClass::NegativeZero => Some(true),
                    FloatClass::Finite { negative, .. } => Some(negative),
                    _ => Some(false),
                }
            }
            _ => None,
        }
    }

    fn eval_fp(&self, expr: &Expr) -> Option<FloatValue> {
        match expr {
            Expr::App(name, args) if name == "fp" => self.eval_fp_constructor(args),
            Expr::App(name, args) if name == "fp.add" => {
                let (a, b) = self.last_two_fp(args)?;
                a.add(
                    &b,
                    self.rounding_mode(args)
                        .unwrap_or(RoundingMode::NearestTiesToEven),
                )
            }
            Expr::App(name, args) if name == "fp.sub" => {
                let (a, b) = self.last_two_fp(args)?;
                a.sub(
                    &b,
                    self.rounding_mode(args)
                        .unwrap_or(RoundingMode::NearestTiesToEven),
                )
            }
            Expr::App(name, args) if name == "fp.mul" => {
                let (a, b) = self.last_two_fp(args)?;
                a.mul(
                    &b,
                    self.rounding_mode(args)
                        .unwrap_or(RoundingMode::NearestTiesToEven),
                )
            }
            Expr::App(name, args) if name == "fp.div" => {
                let (a, b) = self.last_two_fp(args)?;
                a.div(
                    &b,
                    self.rounding_mode(args)
                        .unwrap_or(RoundingMode::NearestTiesToEven),
                )
            }
            Expr::App(name, args) if name == "fp.sqrt" => {
                let fp = args.iter().rev().find_map(|arg| self.eval_fp(arg))?;
                fp.sqrt(
                    self.rounding_mode(args)
                        .unwrap_or(RoundingMode::NearestTiesToEven),
                )
            }
            Expr::App(name, args) if name == "fp.neg" => Some(self.eval_fp(args.first()?)?.neg()),
            Expr::App(name, args) if name == "fp.abs" => Some(self.eval_fp(args.first()?)?.abs()),
            _ => None,
        }
    }

    fn eval_fp_constructor(&self, args: &[Expr]) -> Option<FloatValue> {
        match args {
            [Expr::BvConst(sign, 1), Expr::BvConst(exp, ebits), Expr::BvConst(sig, sig_bits)] => {
                let sort =
                    FloatSort::new((*ebits).try_into().ok()?, (*sig_bits + 1).try_into().ok()?)?;
                let bits = (BigUint::from(*sign) << (*ebits + *sig_bits))
                    | (BigUint::from(*exp) << *sig_bits)
                    | BigUint::from(*sig);
                FloatValue::from_bits(sort, &bits)
            }
            _ => None,
        }
    }

    fn last_two_fp(&self, args: &[Expr]) -> Option<(FloatValue, FloatValue)> {
        let mut vals = args.iter().rev().filter_map(|arg| self.eval_fp(arg));
        let b = vals.next()?;
        let a = vals.next()?;
        Some((a, b))
    }

    fn rounding_mode(&self, args: &[Expr]) -> Option<RoundingMode> {
        args.first().and_then(|arg| match arg {
            Expr::Var(name, _) | Expr::App(name, _) => match name.as_str() {
                "RNE" | "roundNearestTiesToEven" => Some(RoundingMode::NearestTiesToEven),
                "RTZ" | "roundTowardZero" => Some(RoundingMode::TowardZero),
                "RTP" | "roundTowardPositive" => Some(RoundingMode::TowardPositive),
                "RTN" | "roundTowardNegative" => Some(RoundingMode::TowardNegative),
                _ => None,
            },
            _ => None,
        })
    }

    fn fp_eq(&self, a: &FloatValue, b: &FloatValue) -> bool {
        if a.sort != b.sort {
            return false;
        }
        match (&a.class, &b.class) {
            (FloatClass::QuietNaN { .. }, _) | (_, FloatClass::QuietNaN { .. }) => false,
            (
                FloatClass::PositiveZero | FloatClass::NegativeZero,
                FloatClass::PositiveZero | FloatClass::NegativeZero,
            ) => true,
            (FloatClass::PositiveInfinity, FloatClass::PositiveInfinity)
            | (FloatClass::NegativeInfinity, FloatClass::NegativeInfinity) => true,
            (
                FloatClass::Finite {
                    negative: an,
                    value: av,
                },
                FloatClass::Finite {
                    negative: bn,
                    value: bv,
                },
            ) => an == bn && av == bv,
            _ => false,
        }
    }
}

impl TheorySolver for FpSolver {
    fn assert(&mut self, expr: &Expr) {
        if contains_fp(expr) {
            self.assertions.push(expr.clone());
        }
    }

    fn check(&mut self) -> bool {
        self.conflict.clear();
        for assertion in &self.assertions {
            if matches!(self.eval_bool(assertion), Some(false)) {
                self.conflict.push(assertion.clone());
                return false;
            }
        }
        true
    }

    fn explain(&self) -> Vec<Expr> {
        self.conflict.clone()
    }

    fn get_model_value(&self, expr: &Expr) -> Option<ModelValue> {
        self.eval_fp(expr).map(ModelValue::Float)
    }
}

fn contains_fp(expr: &Expr) -> bool {
    match expr {
        Expr::App(name, _) if name == "fp" || name.starts_with("fp.") => true,
        Expr::And(args) | Expr::Or(args) | Expr::Add(args) | Expr::Sub(args) | Expr::Mul(args) => {
            args.iter().any(contains_fp)
        }
        Expr::Not(inner) => contains_fp(inner),
        Expr::Implies(a, b)
        | Expr::Eq(a, b)
        | Expr::Lt(a, b)
        | Expr::Le(a, b)
        | Expr::Gt(a, b)
        | Expr::Ge(a, b)
        | Expr::Div(a, b)
        | Expr::BvAdd(a, b)
        | Expr::BvSub(a, b)
        | Expr::BvMul(a, b)
        | Expr::BvAnd(a, b)
        | Expr::BvOr(a, b)
        | Expr::BvXor(a, b)
        | Expr::BvShl(a, b)
        | Expr::BvLshr(a, b)
        | Expr::BvAshr(a, b)
        | Expr::BvUle(a, b)
        | Expr::BvUlt(a, b)
        | Expr::BvSle(a, b)
        | Expr::BvSlt(a, b)
        | Expr::BvConcat(a, b)
        | Expr::Select(a, b)
        | Expr::StrContains(a, b) => contains_fp(a) || contains_fp(b),
        Expr::BvNot(inner) | Expr::StrLen(inner) => contains_fp(inner),
        Expr::Ite(c, t, e) | Expr::Store(c, t, e) => {
            contains_fp(c) || contains_fp(t) || contains_fp(e)
        }
        Expr::App(_, args) => args.iter().any(contains_fp),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bits32(hex: u32) -> BigUint {
        BigUint::from(hex)
    }

    #[test]
    fn decodes_binary32_one_and_subnormal_exactly() {
        let one = FloatValue::from_bits(FloatSort::BINARY32, &bits32(0x3f80_0000)).unwrap();
        assert_eq!(
            one.class,
            FloatClass::Finite {
                negative: false,
                value: BigRational::one()
            }
        );

        let min_sub = FloatValue::from_bits(FloatSort::BINARY32, &bits32(0x0000_0001)).unwrap();
        assert_eq!(
            min_sub.class,
            FloatClass::Finite {
                negative: false,
                value: pow2_ratio(-149)
            }
        );
    }

    #[test]
    fn encodes_nearest_even_halfway_cases_binary32() {
        let one = BigRational::one();
        let half_ulp = pow2_ratio(-24);
        let tie = FloatValue {
            sort: FloatSort::BINARY32,
            class: FloatClass::Finite {
                negative: false,
                value: one + half_ulp.clone(),
            },
        };
        assert_eq!(
            tie.to_bits(RoundingMode::NearestTiesToEven),
            bits32(0x3f80_0000)
        );

        let above = FloatValue {
            sort: FloatSort::BINARY32,
            class: FloatClass::Finite {
                negative: false,
                value: BigRational::one() + pow2_ratio(-23) + half_ulp,
            },
        };
        assert_eq!(
            above.to_bits(RoundingMode::NearestTiesToEven),
            bits32(0x3f80_0002)
        );
    }

    #[test]
    fn computes_ieee_edge_classes_for_core_ops() {
        let pos_inf = FloatValue::from_bits(FloatSort::BINARY32, &bits32(0x7f80_0000)).unwrap();
        let neg_inf = FloatValue::from_bits(FloatSort::BINARY32, &bits32(0xff80_0000)).unwrap();
        let nan = pos_inf
            .add(&neg_inf, RoundingMode::NearestTiesToEven)
            .unwrap();
        assert!(matches!(nan.class, FloatClass::QuietNaN { .. }));

        let zero = FloatValue::from_bits(FloatSort::BINARY32, &bits32(0x0000_0000)).unwrap();
        let product = zero.mul(&pos_inf, RoundingMode::NearestTiesToEven).unwrap();
        assert!(matches!(product.class, FloatClass::QuietNaN { .. }));

        let four = FloatValue {
            sort: FloatSort::BINARY32,
            class: FloatClass::Finite {
                negative: false,
                value: BigRational::from_integer(BigInt::from(4)),
            },
        };
        let sqrt = four.sqrt(RoundingMode::NearestTiesToEven).unwrap();
        assert_eq!(
            sqrt.to_bits(RoundingMode::NearestTiesToEven),
            bits32(0x4000_0000)
        );
    }
}
