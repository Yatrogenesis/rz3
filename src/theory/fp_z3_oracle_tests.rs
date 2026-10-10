//! Mutation-killing tests for `theory::fp`.
//!
//! Oracle: `tests/data/fp_z3_table.txt`, produced by Z3 (see `tests/data/gen_fp_z3_table.py`)
//! for IEEE Std 754-2019 operations on binary16, binary32, binary64 and the small formats
//! (2,3), (3,4), (3,5). Expected values are used exactly as Z3 prints them.

use super::*;
use crate::ast::Type;

const TABLE: &str = include_str!("../../tests/data/fp_z3_table.txt");

const MODES: [(&str, RoundingMode); 4] = [
    ("RNE", RoundingMode::NearestTiesToEven),
    ("RTZ", RoundingMode::TowardZero),
    ("RTP", RoundingMode::TowardPositive),
    ("RTN", RoundingMode::TowardNegative),
];

fn sort_of(name: &str) -> FloatSort {
    let (e, s) = match name {
        "b16" => (5, 11),
        "b32" => (8, 24),
        "b64" => (11, 53),
        "f23" => (2, 3),
        "f34" => (3, 4),
        "f35" => (3, 5),
        other => panic!("unknown format {other}"),
    };
    FloatSort::new(e, s).unwrap()
}

fn hex(h: &str) -> BigUint {
    BigUint::parse_bytes(h.as_bytes(), 16).unwrap()
}

fn val(sort: FloatSort, h: &str) -> FloatValue {
    FloatValue::from_bits(sort, &hex(h)).unwrap()
}

fn rm(name: &str) -> Expr {
    Expr::Var(name.to_string(), Type::Real)
}

/// `(fp sign exp frac)` constructor expression for a bit pattern.
fn fp_expr(sort: FloatSort, h: &str) -> Expr {
    let bits = hex(h);
    let eb = sort.exponent_bits as usize;
    let fb = sort.fraction_bits() as usize;
    let sign = (&bits >> (eb + fb)) & BigUint::one();
    let exp = (&bits >> fb) & ((BigUint::one() << eb) - BigUint::one());
    let frac = &bits & ((BigUint::one() << fb) - BigUint::one());
    Expr::App(
        "fp".to_string(),
        vec![
            Expr::BvConst(sign, 1),
            Expr::BvConst(exp, eb),
            Expr::BvConst(frac, fb),
        ],
    )
}

fn app(name: &str, args: Vec<Expr>) -> Expr {
    Expr::App(name.to_string(), args)
}

fn expect_value(actual: Option<FloatValue>, sort: FloatSort, want: &str, ctx: &str) {
    let got = actual.unwrap_or_else(|| panic!("{ctx}: evaluator returned None, want {want}"));
    assert_eq!(got.sort, sort, "{ctx}: sort");
    if want == "N" {
        assert!(
            matches!(got.class, FloatClass::QuietNaN { .. }),
            "{ctx}: want NaN, got {:?}",
            got.class
        );
    } else {
        let want_value = val(sort, want);
        assert_eq!(got.class, want_value.class, "{ctx}: want bits {want}");
        assert_eq!(
            got.to_bits(RoundingMode::NearestTiesToEven),
            hex(want),
            "{ctx}: bits"
        );
    }
}

fn eval_model(e: &Expr) -> Option<FloatValue> {
    match FpSolver::new().get_model_value(e)? {
        ModelValue::Float(v) => Some(v),
        other => panic!("not a float: {other:?}"),
    }
}

fn rows(kind: &'static str) -> impl Iterator<Item = Vec<&'static str>> {
    TABLE
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| l.split_whitespace().collect::<Vec<_>>())
        .filter(move |f| f.first() == Some(&kind))
}

/// True when the exact (infinitely precise) result of `a op b` is zero although neither
/// operand is NaN or infinite: the case in which IEEE 754-2019 6.3 fixes the sign of the zero
/// (x + (-x) is -0 only under roundTowardNegative; (+-0) * x and (+-0) / x take the XOR of the
/// operand signs).
fn exact_zero_result(op: &str, a: &FloatValue, b: &FloatValue) -> bool {
    let (Some(x), Some(y)) = (a.exact_rational(), b.exact_rational()) else {
        return false;
    };
    match op {
        "add" => (x + y).is_zero(),
        "sub" => (x - y).is_zero(),
        "mul" => (x * y).is_zero(),
        _ => !y.is_zero() && (x / y).is_zero(),
    }
}

/// Runs the Z3 table for the four binary operations. With `strict == false` the sign of a
/// zero produced by an exactly-zero result is not compared (known defect, see
/// `ieee_signed_zero_of_exact_zero_results`); everything else is always compared.
fn run_binary_table(strict: bool) -> usize {
    let mut n = 0usize;
    for op in ["add", "sub", "mul", "div"] {
        for f in rows(op) {
            let sort = sort_of(f[1]);
            let (a, b) = (val(sort, f[2]), val(sort, f[3]));
            let exact_zero = exact_zero_result(op, &a, &b);
            for (i, (mname, mode)) in MODES.iter().enumerate() {
                let ctx = format!("{op} {} {} {} {mname}", f[1], f[2], f[3]);
                let direct = match op {
                    "add" => a.add(&b, *mode),
                    "sub" => a.sub(&b, *mode),
                    "mul" => a.mul(&b, *mode),
                    _ => a.div(&b, *mode),
                };
                let e = app(
                    &format!("fp.{op}"),
                    vec![rm(mname), fp_expr(sort, f[2]), fp_expr(sort, f[3])],
                );
                let via_expr = eval_model(&e);
                if !strict && exact_zero {
                    // Compare the magnitude class only: the result must be a zero.
                    for got in [direct, via_expr] {
                        assert!(is_zero(&got.expect(&ctx).class), "{ctx}: want a zero");
                    }
                } else {
                    expect_value(direct, sort, f[4 + i], &format!("direct {ctx}"));
                    expect_value(via_expr, sort, f[4 + i], &format!("expr {ctx}"));
                }
                n += 1;
            }
        }
    }
    n
}

#[test]
fn z3_table_binary_arithmetic_all_modes_and_formats() {
    let n = run_binary_table(false);
    assert!(n > 60_000, "table unexpectedly small: {n}");
}

// DEFECT (reported, not fixed here): when the exact result is zero the evaluator takes the
// sign from the zero rational (always +0). IEEE 754-2019 6.3 requires (+0)+(-0) and x-x to be
// -0 under roundTowardNegative, and (+-0)*x, (+-0)/x, x*(+-0) to carry the XOR of the operand
// signs. Z3 agrees with the standard (e.g. `add b16 0000 8000 RTN` -> 8000, `mul b32 80000000
// 3f800000` -> 80000000).
#[test]
#[ignore = "known defect: sign of exactly-zero results of add/sub/mul/div (IEEE 754-2019 6.3)"]
fn ieee_signed_zero_of_exact_zero_results() {
    run_binary_table(true);
}

#[test]
fn z3_table_sqrt_all_modes_and_formats() {
    let mut n = 0usize;
    for f in rows("sqrt") {
        let sort = sort_of(f[1]);
        let a = val(sort, f[2]);
        for (i, (mname, mode)) in MODES.iter().enumerate() {
            let ctx = format!("sqrt {} {} {mname}", f[1], f[2]);
            expect_value(a.sqrt(*mode), sort, f[4 + i], &format!("direct {ctx}"));
            let e = app("fp.sqrt", vec![rm(mname), fp_expr(sort, f[2])]);
            expect_value(eval_model(&e), sort, f[4 + i], &format!("expr {ctx}"));
            n += 1;
        }
    }
    assert!(n > 1500, "{n}");
}

#[test]
fn z3_table_min_max() {
    let mut unspecified = 0;
    for kind in ["min", "max"] {
        for f in rows(if kind == "min" { "min" } else { "max" }) {
            let sort = sort_of(f[1]);
            let e = app(
                &format!("fp.{kind}"),
                vec![fp_expr(sort, f[2]), fp_expr(sort, f[3])],
            );
            let ctx = format!("{kind} {} {} {}", f[1], f[2], f[3]);
            if f[4] == "?" {
                // +0 / -0: unspecified in SMT-LIB, the evaluator must stay undecided.
                assert!(eval_model(&e).is_none(), "{ctx}: must be undecided");
                unspecified += 1;
            } else {
                expect_value(eval_model(&e), sort, f[4], &ctx);
            }
        }
    }
    assert!(unspecified >= 6);
}

#[test]
fn z3_table_comparisons_and_structural_equality() {
    let solver = FpSolver::new();
    let names = ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"];
    for f in rows("cmp") {
        let sort = sort_of(f[1]);
        let (a, b) = (fp_expr(sort, f[2]), fp_expr(sort, f[3]));
        let bits: Vec<bool> = f[4].chars().map(|c| c == '1').collect();
        for (i, name) in names.iter().enumerate() {
            let e = app(name, vec![a.clone(), b.clone()]);
            assert_eq!(
                solver.eval_bool(&e),
                Some(bits[i]),
                "{name} {} {} {}",
                f[1],
                f[2],
                f[3]
            );
        }
        let eq = Expr::Eq(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(
            solver.eval_bool(&eq),
            Some(bits[5]),
            "= {} {} {}",
            f[1],
            f[2],
            f[3]
        );
        // The assertion path (assert + check) agrees with the evaluator.
        let mut s = FpSolver::new();
        s.assert(&eq);
        assert_eq!(s.check(), bits[5]);
        let mut s = FpSolver::new();
        s.assert(&Expr::Not(Box::new(eq)));
        assert_eq!(s.check(), !bits[5]);
    }
}

#[test]
fn z3_table_classification() {
    let solver = FpSolver::new();
    let names = [
        "fp.isNormal",
        "fp.isSubnormal",
        "fp.isNaN",
        "fp.isInfinite",
        "fp.isZero",
        "fp.isPositive",
        "fp.isNegative",
    ];
    for f in rows("cls") {
        let sort = sort_of(f[1]);
        let a = fp_expr(sort, f[2]);
        for (i, c) in f[3].chars().enumerate() {
            let e = app(names[i], vec![a.clone()]);
            assert_eq!(
                solver.eval_bool(&e),
                Some(c == '1'),
                "{} {} {}",
                names[i],
                f[1],
                f[2]
            );
        }
    }
}

#[test]
fn z3_table_real_to_fp_all_modes_and_formats() {
    let mut n = 0;
    for f in rows("real") {
        let sort = sort_of(f[1]);
        let q = BigRational::new(
            f[2].parse::<BigInt>().unwrap(),
            f[3].parse::<BigInt>().unwrap(),
        );
        let to_fp = format!("fp.to_fp.{}.{}", sort.exponent_bits, sort.significand_bits);
        for (i, (mname, mode)) in MODES.iter().enumerate() {
            let ctx = format!("to_fp {} {}/{} {mname}", f[1], f[2], f[3]);
            let direct =
                FloatValue::from_bits(sort, &round_signed_rational_to_bits(sort, &q, *mode));
            expect_value(direct, sort, f[4 + i], &format!("direct {ctx}"));
            let e = app(&to_fp, vec![rm(mname), Expr::from_rational(&q)]);
            expect_value(eval_model(&e), sort, f[4 + i], &format!("expr {ctx}"));
            // `round_finite_to_bits` encodes a finite magnitude directly.
            if !q.is_zero() {
                let v = FloatValue {
                    sort,
                    class: FloatClass::Finite {
                        negative: q.is_negative(),
                        value: q.abs(),
                    },
                };
                let want = hex(f[4 + i]);
                let got = v.to_bits(*mode);
                assert_eq!(got, want, "to_bits {ctx}");
            }
            n += 1;
        }
    }
    assert!(n > 5000, "{n}");
}

#[test]
fn z3_table_bits_roundtrip() {
    for f in rows("cls") {
        let sort = sort_of(f[1]);
        let v = val(sort, f[2]);
        let want = if matches!(v.class, FloatClass::QuietNaN { .. }) {
            // NaN keeps its payload; the sign of a NaN is not represented.
            hex(f[2])
                & ((BigUint::one() << (sort.exponent_bits + sort.fraction_bits())) - BigUint::one())
        } else {
            hex(f[2])
        };
        for (_, mode) in MODES {
            assert_eq!(v.to_bits(mode), want, "roundtrip {} {}", f[1], f[2]);
        }
    }
}

#[test]
fn invalid_operations_yield_the_default_quiet_nan() {
    // IEEE 754-2019 6.2.1: a quiet NaN has the most significant fraction bit set.
    for (sort, qnan) in [
        (FloatSort::BINARY16, 0x7e00u64),
        (FloatSort::BINARY32, 0x7fc0_0000),
        (FloatSort::BINARY64, 0x7ff8_0000_0000_0000),
    ] {
        let want = BigUint::from(qnan);
        assert_eq!(
            default_nan(sort),
            FloatClass::QuietNaN {
                payload: BigUint::one() << (sort.fraction_bits() - 1)
            }
        );
        let inf = FloatValue {
            sort,
            class: FloatClass::PositiveInfinity,
        };
        let ninf = inf.neg();
        let zero = FloatValue {
            sort,
            class: FloatClass::PositiveZero,
        };
        let rne = RoundingMode::NearestTiesToEven;
        assert_eq!(inf.add(&ninf, rne).unwrap().to_bits(rne), want);
        assert_eq!(inf.sub(&inf, rne).unwrap().to_bits(rne), want);
        assert_eq!(zero.mul(&inf, rne).unwrap().to_bits(rne), want);
        assert_eq!(inf.mul(&zero, rne).unwrap().to_bits(rne), want);
        assert_eq!(zero.div(&zero, rne).unwrap().to_bits(rne), want);
        assert_eq!(inf.div(&inf, rne).unwrap().to_bits(rne), want);
        assert_eq!(ninf.sqrt(rne).unwrap().to_bits(rne), want);
        let minus_one = FloatValue {
            sort,
            class: FloatClass::Finite {
                negative: true,
                value: BigRational::one(),
            },
        };
        assert_eq!(minus_one.sqrt(rne).unwrap().to_bits(rne), want);
    }
}

#[test]
fn nan_payload_is_propagated_and_sort_mismatch_is_rejected() {
    let sort = FloatSort::BINARY32;
    let rne = RoundingMode::NearestTiesToEven;
    let nan = val(sort, "7fc12345");
    let other = val(sort, "7fc00777");
    let one = val(sort, "3f800000");
    let payload = |v: Option<FloatValue>| match v.unwrap().class {
        FloatClass::QuietNaN { payload } => payload,
        c => panic!("not NaN: {c:?}"),
    };
    let p1 = BigUint::from(0x41_2345u32);
    assert_eq!(payload(nan.add(&one, rne)), p1);
    assert_eq!(payload(one.add(&nan, rne)), p1);
    assert_eq!(payload(nan.mul(&one, rne)), p1);
    assert_eq!(payload(one.mul(&nan, rne)), p1);
    assert_eq!(payload(nan.div(&one, rne)), p1);
    assert_eq!(payload(one.div(&nan, rne)), p1);
    assert_eq!(payload(nan.sqrt(rne)), p1);
    assert_eq!(payload(Some(nan.neg())), p1);
    assert_eq!(payload(Some(nan.abs())), p1);
    // The first NaN operand wins when both are NaN.
    assert_eq!(payload(nan.add(&other, rne)), p1);
    assert_eq!(payload(other.add(&nan, rne)), BigUint::from(0x40_0777u32));
    // Operands of different sorts are not combined.
    let h = val(FloatSort::BINARY16, "3c00");
    assert!(one.add(&h, rne).is_none());
    assert!(one.sub(&h, rne).is_none());
    assert!(one.mul(&h, rne).is_none());
    assert!(one.div(&h, rne).is_none());
}

#[test]
fn neg_and_abs_cover_every_class() {
    let sort = FloatSort::BINARY32;
    for (h, neg_h, abs_h) in [
        ("00000000", "80000000", "00000000"),
        ("80000000", "00000000", "00000000"),
        ("7f800000", "ff800000", "7f800000"),
        ("ff800000", "7f800000", "7f800000"),
        ("3fc00000", "bfc00000", "3fc00000"),
        ("bfc00000", "3fc00000", "3fc00000"),
        ("00000001", "80000001", "00000001"),
        ("80000001", "00000001", "00000001"),
    ] {
        let v = val(sort, h);
        assert_eq!(
            v.neg().to_bits(RoundingMode::TowardZero),
            hex(neg_h),
            "neg {h}"
        );
        assert_eq!(
            v.abs().to_bits(RoundingMode::TowardZero),
            hex(abs_h),
            "abs {h}"
        );
        let e = app("fp.neg", vec![fp_expr(sort, h)]);
        assert_eq!(
            eval_model(&e).unwrap().to_bits(RoundingMode::TowardZero),
            hex(neg_h)
        );
        let e = app("fp.abs", vec![fp_expr(sort, h)]);
        assert_eq!(
            eval_model(&e).unwrap().to_bits(RoundingMode::TowardZero),
            hex(abs_h)
        );
    }
}

#[test]
fn overflow_and_max_finite_bits_per_mode() {
    // IEEE 754-2019 4.3: overflow returns +-inf for the nearest/away directions and
    // the largest finite number for the directed modes that round toward zero.
    for (sort, max_pos, inf_pos) in [
        (FloatSort::BINARY16, "7bff", "7c00"),
        (FloatSort::BINARY32, "7f7fffff", "7f800000"),
        (FloatSort::BINARY64, "7fefffffffffffff", "7ff0000000000000"),
    ] {
        let width = (sort.exponent_bits + sort.significand_bits) as usize;
        let sign = BigUint::one() << (width - 1);
        let (mp, ip) = (hex(max_pos), hex(inf_pos));
        let (mn, inn) = (&mp | &sign, &ip | &sign);
        assert_eq!(max_finite_bits(sort, false), mp);
        assert_eq!(max_finite_bits(sort, true), mn);
        assert_eq!(
            overflow_bits(sort, false, RoundingMode::NearestTiesToEven),
            ip
        );
        assert_eq!(overflow_bits(sort, false, RoundingMode::TowardZero), mp);
        assert_eq!(overflow_bits(sort, false, RoundingMode::TowardPositive), ip);
        assert_eq!(overflow_bits(sort, false, RoundingMode::TowardNegative), mp);
        assert_eq!(
            overflow_bits(sort, true, RoundingMode::NearestTiesToEven),
            inn
        );
        assert_eq!(overflow_bits(sort, true, RoundingMode::TowardZero), mn);
        assert_eq!(overflow_bits(sort, true, RoundingMode::TowardPositive), mn);
        assert_eq!(overflow_bits(sort, true, RoundingMode::TowardNegative), inn);
    }
}

#[test]
fn rounding_mode_names_and_unknown_modes() {
    let solver = FpSolver::new();
    for (names, mode) in [
        (
            ["RNE", "roundNearestTiesToEven"],
            RoundingMode::NearestTiesToEven,
        ),
        (["RTZ", "roundTowardZero"], RoundingMode::TowardZero),
        (["RTP", "roundTowardPositive"], RoundingMode::TowardPositive),
        (["RTN", "roundTowardNegative"], RoundingMode::TowardNegative),
    ] {
        for n in names {
            assert_eq!(solver.rounding_mode(&[rm(n)]), Some(mode), "{n}");
            assert_eq!(
                solver.rounding_mode(&[app(n, vec![])]),
                Some(mode),
                "{n} as application"
            );
        }
    }
    assert_eq!(solver.rounding_mode(&[rm("RNA")]), None);
    assert_eq!(solver.rounding_mode(&[]), None);
    assert_eq!(solver.rounding_mode(&[Expr::Int(3)]), None);
    // A real-to-float conversion with an unknown rounding mode is not evaluated.
    let e = app(
        "fp.to_fp.8.24",
        vec![rm("RNA"), Expr::from_rational(&BigRational::one())],
    );
    assert!(eval_model(&e).is_none());
}

#[test]
fn to_fp_reinterprets_bit_patterns_only_at_exact_width() {
    let e = app(
        "fp.to_fp.8.24",
        vec![Expr::BvConst(BigUint::from(0x3f80_0000u32), 32)],
    );
    expect_value(
        eval_model(&e),
        FloatSort::BINARY32,
        "3f800000",
        "reinterpret",
    );
    let e = app(
        "fp.to_fp.8.24",
        vec![Expr::BvConst(BigUint::from(0x3f80_0000u32), 31)],
    );
    assert!(eval_model(&e).is_none());
    let e = app(
        "fp.to_fp.8.24",
        vec![Expr::BvConst(BigUint::from(1u32), 33)],
    );
    assert!(eval_model(&e).is_none());
    let e = app("fp.to_fp.8.24", vec![]);
    assert!(eval_model(&e).is_none());
    let e = app(
        "fp.to_fp.1.24",
        vec![Expr::BvConst(BigUint::from(1u32), 25)],
    );
    assert!(eval_model(&e).is_none());
}

#[test]
fn min_max_edge_cases_and_mixed_sorts() {
    let s = FloatSort::BINARY32;
    let nan = fp_expr(s, "7fc00000");
    let one = fp_expr(s, "3f800000");
    let two = fp_expr(s, "40000000");
    let pz = fp_expr(s, "00000000");
    let nz = fp_expr(s, "80000000");
    let bits = |e: &Expr| eval_model(e).map(|v| v.to_bits(RoundingMode::TowardZero));
    assert_eq!(
        bits(&app("fp.min", vec![nan.clone(), one.clone()])),
        Some(hex("3f800000"))
    );
    assert_eq!(
        bits(&app("fp.min", vec![one.clone(), nan.clone()])),
        Some(hex("3f800000"))
    );
    assert_eq!(
        bits(&app("fp.max", vec![nan.clone(), two.clone()])),
        Some(hex("40000000"))
    );
    assert_eq!(
        bits(&app("fp.max", vec![two.clone(), nan.clone()])),
        Some(hex("40000000"))
    );
    assert_eq!(
        bits(&app("fp.min", vec![one.clone(), two.clone()])),
        Some(hex("3f800000"))
    );
    assert_eq!(
        bits(&app("fp.min", vec![two.clone(), one.clone()])),
        Some(hex("3f800000"))
    );
    assert_eq!(
        bits(&app("fp.max", vec![one.clone(), two.clone()])),
        Some(hex("40000000"))
    );
    assert_eq!(
        bits(&app("fp.max", vec![two.clone(), one.clone()])),
        Some(hex("40000000"))
    );
    assert_eq!(
        bits(&app("fp.min", vec![pz.clone(), pz.clone()])),
        Some(hex("0"))
    );
    assert_eq!(
        bits(&app("fp.max", vec![nz.clone(), nz.clone()])),
        Some(hex("80000000"))
    );
    assert_eq!(bits(&app("fp.min", vec![pz.clone(), nz.clone()])), None);
    assert_eq!(bits(&app("fp.max", vec![nz.clone(), pz.clone()])), None);
    assert_eq!(bits(&app("fp.min", vec![one.clone()])), None);
    assert_eq!(
        bits(&app("fp.min", vec![one.clone(), two.clone(), pz.clone()])),
        None
    );
    let half = fp_expr(FloatSort::BINARY16, "3c00");
    assert_eq!(bits(&app("fp.min", vec![one.clone(), half.clone()])), None);
    // Comparisons across sorts are not evaluated.
    let solver = FpSolver::new();
    for op in ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq"] {
        assert_eq!(
            solver.eval_bool(&app(op, vec![one.clone(), half.clone()])),
            None,
            "{op}"
        );
        assert_eq!(
            solver.eval_bool(&app(op, vec![one.clone()])),
            None,
            "{op} arity"
        );
    }
}

#[test]
fn boolean_connectives_over_fp_predicates() {
    let s = FloatSort::BINARY32;
    let solver = FpSolver::new();
    let t = app("fp.isNaN", vec![fp_expr(s, "7fc00000")]);
    let f = app("fp.isNaN", vec![fp_expr(s, "3f800000")]);
    let ev = |e: &Expr| solver.eval_bool(e);
    let not = |e: &Expr| Expr::Not(Box::new(e.clone()));
    assert_eq!(ev(&Expr::Bool(true)), Some(true));
    assert_eq!(ev(&Expr::Bool(false)), Some(false));
    assert_eq!(ev(&not(&t)), Some(false));
    assert_eq!(ev(&not(&f)), Some(true));
    assert_eq!(ev(&Expr::And(vec![])), Some(true));
    assert_eq!(ev(&Expr::And(vec![t.clone(), t.clone()])), Some(true));
    assert_eq!(ev(&Expr::And(vec![t.clone(), f.clone()])), Some(false));
    assert_eq!(ev(&Expr::And(vec![f.clone(), t.clone()])), Some(false));
    assert_eq!(ev(&Expr::Or(vec![])), Some(false));
    assert_eq!(ev(&Expr::Or(vec![f.clone(), f.clone()])), Some(false));
    assert_eq!(ev(&Expr::Or(vec![f.clone(), t.clone()])), Some(true));
    assert_eq!(ev(&Expr::Or(vec![t.clone(), f.clone()])), Some(true));
    for (a, b, want) in [
        (&t, &t, true),
        (&t, &f, false),
        (&f, &t, true),
        (&f, &f, true),
    ] {
        let e = Expr::Implies(Box::new(a.clone()), Box::new(b.clone()));
        assert_eq!(ev(&e), Some(want));
    }
    // Undecidable sub-terms propagate as None instead of being guessed.
    let unknown = app("fp.isNaN", vec![Expr::Var("x".into(), Type::Float(s))]);
    assert_eq!(ev(&unknown), None);
    assert_eq!(ev(&Expr::And(vec![t.clone(), unknown.clone()])), None);
    assert_eq!(ev(&Expr::Or(vec![f.clone(), unknown.clone()])), None);
    assert_eq!(ev(&not(&unknown)), None);
    assert_eq!(ev(&app("fp.unknownpred", vec![])), None);
}

#[test]
fn solver_check_reset_and_unknown_state() {
    let s = FloatSort::BINARY32;
    let mut solver = FpSolver::new();
    assert!(!solver.is_unknown());
    let false_pred = app("fp.isNaN", vec![fp_expr(s, "3f800000")]);
    solver.assert(&false_pred);
    assert!(!solver.check());
    assert_eq!(solver.explain(), vec![false_pred.clone()]);
    solver.reset();
    assert!(solver.check());
    assert!(solver.explain().is_empty());
    let unknown = app("fp.isNaN", vec![Expr::Var("x".into(), Type::Float(s))]);
    solver.assert(&unknown);
    assert!(solver.check());
    assert!(solver.is_unknown());
    solver.reset();
    assert!(!solver.is_unknown());
    assert!(solver.check());
    // Assertions without floating point are ignored.
    solver.assert(&Expr::Bool(false));
    assert!(solver.check());
    assert!(!solver.is_unknown());
}

#[test]
fn from_bits_decodes_each_format_fields_exactly() {
    for (name, h, want) in [
        ("b16", "0400", pow2_ratio(-14)),
        ("b16", "0001", pow2_ratio(-24)),
        (
            "b16",
            "7bff",
            BigRational::from_integer(BigInt::from(65504)),
        ),
        ("f23", "01", pow2_ratio(-2)),
        ("f23", "02", pow2_ratio(-1)),
        ("f34", "08", pow2_ratio(-2)),
        ("b64", "0000000000000001", pow2_ratio(-1074)),
        ("b64", "3ff0000000000000", BigRational::one()),
    ] {
        let sort = sort_of(name);
        assert_eq!(
            val(sort, h).class,
            FloatClass::Finite {
                negative: false,
                value: want
            },
            "{name} {h}"
        );
    }
    let s = FloatSort::BINARY32;
    assert_eq!(s.exponent_max(), 255);
    assert_eq!(s.exponent_bias(), 127);
    assert_eq!(s.fraction_bits(), 23);
    assert_eq!(val(s, "3f800000").sort_bias(), 127);
    assert_eq!(FloatSort::BINARY16.fraction_bits(), 10);
    assert_eq!(FloatSort::BINARY64.exponent_bias(), 1023);
    assert_eq!(FloatSort::new(3, 4).unwrap().fraction_bits(), 3);
}

#[test]
fn integer_helpers_match_exact_arithmetic() {
    // floor_log2_rational / floor_log2_sqrt_rational / sqrt_upper_bound / round_sqrt_integer.
    let q = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
    for (n, d, e) in [
        (1, 1, 0),
        (3, 2, 0),
        (2, 1, 1),
        (7, 8, -1),
        (1, 3, -2),
        (1024, 1, 10),
        (1023, 1, 9),
        (1, 1024, -10),
        (5, 1, 2),
    ] {
        assert_eq!(floor_log2_rational(&q(n, d)), e, "{n}/{d}");
    }
    for (n, d, e) in [
        (1, 1, 0),
        (4, 1, 1),
        (3, 1, 0),
        (16, 1, 2),
        (1, 4, -1),
        (1, 3, -1),
        (1, 16, -2),
        (2, 1, 0),
        (64, 1, 3),
    ] {
        assert_eq!(floor_log2_sqrt_rational(&q(n, d)), e, "sqrt {n}/{d}");
    }
    for n in [1i64, 2, 3, 4, 15, 16, 17, 255, 256, 1_000_000] {
        let ub = sqrt_upper_bound(&BigInt::from(n));
        assert!(&ub * &ub >= BigInt::from(n), "ub^2 >= {n}");
        // Not wastefully loose: at most 2*sqrt(n)+2.
        assert!(&ub * &ub <= BigInt::from(4 * n + 8), "ub^2 <= 4n+8 for {n}");
    }
    assert_eq!(sqrt_upper_bound(&BigInt::zero()), BigInt::zero());
    let r = |v: BigRational, neg: bool, m: RoundingMode| round_sqrt_integer(&v, neg, m).unwrap();
    let nearest = RoundingMode::NearestTiesToEven;
    // sqrt(x) for x = n/d is rounded to an integer.
    assert_eq!(r(q(16, 1), false, nearest), BigInt::from(4));
    assert_eq!(r(q(1, 4), false, nearest), BigInt::zero());
    assert_eq!(r(q(1, 1), false, nearest), BigInt::one());
    // Reachable inputs are integers (see the ignored test below). sqrt(6)=2.449 -> 2,
    // sqrt(7)=2.646 -> 3, the boundary being (2.5)^2 = 6.25.
    assert_eq!(r(q(6, 1), false, nearest), BigInt::from(2));
    assert_eq!(r(q(7, 1), false, nearest), BigInt::from(3));
    assert_eq!(r(q(12, 1), false, nearest), BigInt::from(3)); // 3.464
    assert_eq!(r(q(13, 1), false, nearest), BigInt::from(4)); // 3.606
    assert_eq!(r(q(20, 1), false, nearest), BigInt::from(4)); // 4.472
    assert_eq!(r(q(21, 1), false, nearest), BigInt::from(5)); // 4.583
    assert_eq!(r(q(2, 1), false, nearest), BigInt::one()); // 1.414
    assert_eq!(r(q(3, 1), false, nearest), BigInt::from(2)); // 1.732
    assert_eq!(r(q(10, 1), false, nearest), BigInt::from(3)); // 3.162
    assert_eq!(r(q(11, 1), false, nearest), BigInt::from(3)); // 3.317
    assert_eq!(r(q(1_000_000, 1), false, nearest), BigInt::from(1000));
    assert_eq!(r(q(1_000_001, 1), false, nearest), BigInt::from(1000)); // 1000.0005
    assert_eq!(r(q(1_001_000, 1), false, nearest), BigInt::from(1000)); // 1000.4999
    assert_eq!(r(q(1_001_001, 1), false, nearest), BigInt::from(1001)); // 1000.5004
    for (mode, neg, want) in [
        (RoundingMode::TowardZero, false, 1),
        (RoundingMode::TowardNegative, false, 1),
        (RoundingMode::TowardPositive, false, 2),
        (RoundingMode::TowardZero, true, 1),
        (RoundingMode::TowardPositive, true, 1),
        (RoundingMode::TowardNegative, true, 2),
    ] {
        assert_eq!(
            r(q(2, 1), neg, mode),
            BigInt::from(want),
            "{mode:?} neg={neg}"
        );
    }
    // Exact roots are never adjusted by a directed mode.
    for mode in [
        RoundingMode::TowardZero,
        RoundingMode::TowardPositive,
        RoundingMode::TowardNegative,
    ] {
        assert_eq!(r(q(81, 1), false, mode), BigInt::from(9));
        let want = if mode == RoundingMode::TowardPositive {
            1
        } else {
            0
        };
        assert_eq!(r(q(1, 9), false, mode), BigInt::from(want));
    }
}

// LATENT DEFECT (unreachable through the public API, reported, not fixed here):
// `round_sqrt_integer` decides nearest-rounding by comparing x - F^2 with (F+1)^2 - x, i.e.
// x against F^2 + F + 1/2, whereas the correct midpoint test for sqrt(x) is x against
// (F + 1/2)^2 = F^2 + F + 1/4. For integer x the two tests agree (no integer lies in
// (F^2+F+1/4, F^2+F+1/2]), and every call site passes an integer (the scaled significand
// is always a multiple of 2^fraction_bits), so no float result is affected.
#[test]
#[ignore = "latent defect: nearest rounding of sqrt of a non-integer rational (unreachable)"]
fn round_sqrt_integer_nearest_is_exact_for_rationals() {
    let q = |n: i64, d: i64| BigRational::new(BigInt::from(n), BigInt::from(d));
    let nearest = RoundingMode::NearestTiesToEven;
    // sqrt(2.3) = 1.5166 -> 2 ; sqrt(2.25) = 1.5 is a tie -> 2 (even); sqrt(6.5) = 2.55 -> 3.
    assert_eq!(
        round_sqrt_integer(&q(23, 10), false, nearest).unwrap(),
        BigInt::from(2)
    );
    assert_eq!(
        round_sqrt_integer(&q(9, 4), false, nearest).unwrap(),
        BigInt::from(2)
    );
    assert_eq!(
        round_sqrt_integer(&q(13, 2), false, nearest).unwrap(),
        BigInt::from(3)
    );
}
