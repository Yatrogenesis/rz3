// Tests for the exact evaluator (`rz3::eval`), the independent check that certifies every
// `sat` verdict. Expected values come from tests/data/eval_cases_*.txt (computed by hand or
// from the SMT-LIB definitional expansions, and contrasted with Z3 by
// tests/data/verify_eval_cases_z3.py) plus the directly-constructed edge cases below.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Zero};
use rz3::ast::{Expr, ModelValue, Type};
use rz3::eval::{eval, eval_with, holds, FunTable, Value, Verdict};
use rz3::parser::{Command, Parser};
use std::collections::BTreeMap;

type Model = BTreeMap<String, ModelValue>;

fn render(v: &Option<Value>) -> String {
    match v {
        None => "unknown".to_string(),
        Some(Value::Bool(b)) => b.to_string(),
        Some(Value::Num(r)) => {
            if r.is_integer() {
                r.numer().to_string()
            } else {
                format!("{}/{}", r.numer(), r.denom())
            }
        }
        Some(Value::Bv(v, w)) => {
            let s = v.to_str_radix(2);
            let s = if v.is_zero() { String::new() } else { s };
            format!("#b{}{}", "0".repeat(w.saturating_sub(s.len())), s)
        }
    }
}

fn parse_rational(s: &str) -> BigRational {
    match s.split_once('/') {
        Some((n, d)) => BigRational::new(n.parse().unwrap(), d.parse().unwrap()),
        None => BigRational::from_integer(s.parse().unwrap()),
    }
}

fn parse_bits(s: &str) -> (BigUint, usize) {
    if let Some(h) = s.strip_prefix("#x") {
        (BigUint::parse_bytes(h.as_bytes(), 16).unwrap(), h.len() * 4)
    } else {
        let b = s.strip_prefix("#b").unwrap();
        (BigUint::parse_bytes(b.as_bytes(), 2).unwrap(), b.len())
    }
}

/// `x:Int=5,y:bv8=#x0f` -> SMT-LIB declarations plus a model.
fn parse_vars(spec: &str) -> (String, Model) {
    let mut decls = String::new();
    let mut model = Model::new();
    if spec.is_empty() {
        return (decls, model);
    }
    for d in spec.split(',') {
        let (name, rest) = d.split_once(':').unwrap();
        let (sort, val) = rest.split_once('=').unwrap();
        let (smt_sort, mv) = match sort {
            "Int" => ("Int".to_string(), ModelValue::Int(val.parse().unwrap())),
            "Real" => ("Real".to_string(), ModelValue::Real(parse_rational(val))),
            "Bool" => ("Bool".to_string(), ModelValue::Bool(val == "true")),
            _ => {
                let w: usize = sort.strip_prefix("bv").unwrap().parse().unwrap();
                let (v, _) = parse_bits(val);
                (format!("(_ BitVec {w})"), ModelValue::BitVec(v, w))
            }
        };
        decls.push_str(&format!("(declare-fun {name} () {smt_sort})"));
        model.insert(name.to_string(), mv);
    }
    (decls, model)
}

fn parse_expr(decls: &str, expr: &str) -> Expr {
    let src = format!("{decls}(assert {expr})");
    let mut p = Parser::new(&src);
    let mut found = None;
    while let Some(c) = p.parse_command() {
        if let Command::Assert(e) = c {
            found = Some(e);
        }
    }
    assert!(p.error().is_none(), "parse error in {src}: {:?}", p.error());
    found.unwrap_or_else(|| panic!("no assertion parsed from {src}"))
}

fn run_table(text: &str, name: &str) -> usize {
    let mut failures = Vec::new();
    let mut n = 0;
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split(" ; ").collect();
        assert_eq!(parts.len(), 3, "bad case line in {name}: {line}");
        let (decls, model) = parse_vars(parts[0].trim());
        let e = parse_expr(&decls, parts[1].trim());
        let got = render(&eval(&e, &model));
        n += 1;
        if got != parts[2].trim() {
            failures.push(format!("{line}   -- got {got}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {n} cases in {name} differ:\n{}",
        failures.len(),
        failures
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    n
}

#[test]
fn table_arith_bool_and_unknown() {
    let n = run_table(include_str!("data/eval_cases_arith.txt"), "arith");
    assert!(n >= 160, "case count must not shrink (got {n})");
}

#[test]
fn table_bitvector_widths_1_8_64_100() {
    let n = run_table(include_str!("data/eval_cases_bv.txt"), "bv");
    assert!(n >= 4800, "case count must not shrink (got {n})");
}

// ---------------------------------------------------------------- direct constructions

fn b(e: Expr) -> Box<Expr> {
    Box::new(e)
}
fn int(i: i64) -> Expr {
    Expr::Int(i)
}
fn bvc(v: u64, w: usize) -> Expr {
    Expr::BvConst(BigUint::from(v), w)
}
fn num(n: i64, d: i64) -> Option<Value> {
    Some(Value::Num(BigRational::new(n.into(), d.into())))
}
fn bv(v: u64, w: usize) -> Option<Value> {
    Some(Value::Bv(BigUint::from(v), w))
}
fn ev(e: &Expr) -> Option<Value> {
    eval(e, &Model::new())
}
fn tru() -> Expr {
    Expr::Bool(true)
}
fn zero_bits(w: usize) -> Expr {
    Expr::BvConst(BigUint::zero(), w)
}

#[test]
fn literals_masking_and_bigrat() {
    assert_eq!(ev(&tru()), Some(Value::Bool(true)));
    assert_eq!(ev(&Expr::Real(-125, 2)), num(-5, 4));
    assert_eq!(ev(&Expr::Real(7, 0)), num(7, 1));
    // BvConst is reduced modulo 2^w even when built with stray high bits.
    assert_eq!(ev(&bvc(0x1ff, 8)), bv(0xff, 8));
    assert_eq!(ev(&bvc(0x100, 8)), bv(0, 8));
    let wide = (BigUint::one() << 100u32) | BigUint::from(5u8);
    assert_eq!(
        ev(&Expr::BvConst(wide, 100)),
        Some(Value::Bv(BigUint::from(5u8), 100))
    );
    // BigRat: arbitrary precision literal, zero denominator and garbage give None.
    let big = "123456789012345678901234567890";
    assert_eq!(
        ev(&Expr::BigRat(big.into(), "3".into())),
        Some(Value::Num(BigRational::new(
            big.parse::<BigInt>().unwrap(),
            3.into()
        )))
    );
    assert_eq!(ev(&Expr::BigRat("1".into(), "0".into())), None);
    assert_eq!(ev(&Expr::BigRat("x".into(), "2".into())), None);
}

#[test]
fn variables_default_and_declared_sort() {
    let mut m = Model::new();
    let v = |n: &str, t: Type| Expr::Var(n.to_string(), t);
    // absent -> default of the sort
    assert_eq!(eval(&v("p", Type::Bool), &m), Some(Value::Bool(false)));
    assert_eq!(eval(&v("p", Type::Int), &m), num(0, 1));
    assert_eq!(eval(&v("p", Type::Real), &m), num(0, 1));
    assert_eq!(eval(&v("p", Type::BitVec(12)), &m), bv(0, 12));
    assert_eq!(eval(&v("p", Type::String), &m), None);
    assert_eq!(
        eval(
            &v("p", Type::Array(Box::new(Type::Int), Box::new(Type::Int))),
            &m
        ),
        None
    );
    // present with the matching variant
    m.insert("i".into(), ModelValue::Int((-9).into()));
    m.insert(
        "r".into(),
        ModelValue::Real(BigRational::new(3.into(), 4.into())),
    );
    m.insert("t".into(), ModelValue::Bool(true));
    assert_eq!(eval(&v("i", Type::Int), &m), num(-9, 1));
    assert_eq!(eval(&v("r", Type::Real), &m), num(3, 4));
    assert_eq!(eval(&v("t", Type::Bool), &m), Some(Value::Bool(true)));
    // the model's bit-vector width is only a hint: the declared sort wins and truncates
    m.insert("w".into(), ModelValue::BitVec(BigUint::from(0x1abu32), 4));
    assert_eq!(eval(&v("w", Type::BitVec(8)), &m), bv(0xab, 8));
    assert_eq!(eval(&v("w", Type::BitVec(16)), &m), bv(0x1ab, 16));
    // declared sort that is not a bit-vector: the model's own pattern and width are kept
    assert_eq!(eval(&v("w", Type::Int), &m), bv(0x1ab, 4));
}

#[test]
fn boolean_connectives_do_not_short_circuit_over_unknowns() {
    let q = Expr::ForAll(vec![("i".into(), Type::Int)], b(tru()));
    for e in [
        Expr::And(vec![Expr::Bool(false), q.clone()]),
        Expr::Or(vec![tru(), q.clone()]),
        Expr::Implies(b(Expr::Bool(false)), b(q.clone())),
        Expr::Implies(b(q.clone()), b(tru())),
        Expr::Not(b(q.clone())),
        Expr::Ite(b(q.clone()), b(int(1)), b(int(2))),
    ] {
        assert_eq!(ev(&e), None, "{e:?}");
    }
    // empty conjunction / disjunction
    assert_eq!(ev(&Expr::And(vec![])), Some(Value::Bool(true)));
    assert_eq!(ev(&Expr::Or(vec![])), Some(Value::Bool(false)));
    // non-Boolean operands are not coerced
    assert_eq!(ev(&Expr::Not(b(int(1)))), None);
    assert_eq!(ev(&Expr::And(vec![int(1)])), None);
    assert_eq!(ev(&Expr::Or(vec![int(0)])), None);
    assert_eq!(ev(&Expr::Implies(b(int(1)), b(tru()))), None);
    assert_eq!(ev(&Expr::Implies(b(tru()), b(int(1)))), None);
    assert_eq!(ev(&Expr::Ite(b(int(1)), b(int(1)), b(int(2)))), None);
    // the untaken branch of an ite is not evaluated
    assert_eq!(ev(&Expr::Ite(b(tru()), b(int(1)), b(q.clone()))), num(1, 1));
    assert_eq!(
        ev(&Expr::Ite(b(Expr::Bool(false)), b(q), b(int(2)))),
        num(2, 1)
    );
}

#[test]
fn equality_across_sorts_and_unknowns() {
    // different value kinds are simply unequal
    assert_eq!(
        ev(&Expr::Eq(b(int(1)), b(bvc(1, 8)))),
        Some(Value::Bool(false))
    );
    assert_eq!(ev(&Expr::Eq(b(tru()), b(int(1)))), Some(Value::Bool(false)));
    // same pattern, different width: unequal
    assert_eq!(
        ev(&Expr::Eq(b(bvc(1, 8)), b(bvc(1, 9)))),
        Some(Value::Bool(false))
    );
    let bad = Expr::IntDiv(b(int(1)), b(int(0)));
    assert_eq!(ev(&Expr::Eq(b(bad.clone()), b(int(1)))), None);
    assert_eq!(ev(&Expr::Eq(b(int(1)), b(bad))), None);
}

#[test]
fn comparisons_require_numbers() {
    for mk in [
        (|a, c| Expr::Lt(a, c)) as fn(Box<Expr>, Box<Expr>) -> Expr,
        |a, c| Expr::Le(a, c),
        |a, c| Expr::Gt(a, c),
        |a, c| Expr::Ge(a, c),
    ] {
        assert_eq!(ev(&mk(b(tru()), b(tru()))), None);
        assert_eq!(ev(&mk(b(int(1)), b(tru()))), None);
        assert_eq!(ev(&mk(b(tru()), b(int(1)))), None);
        assert_eq!(ev(&mk(b(bvc(1, 8)), b(bvc(2, 8)))), None);
    }
    // each operator separately on <, =, >
    let cmp = |ctor: fn(Box<Expr>, Box<Expr>) -> Expr| -> Vec<bool> {
        [(1, 2), (2, 2), (3, 2)]
            .iter()
            .map(|&(x, y)| matches!(ev(&ctor(b(int(x)), b(int(y)))), Some(Value::Bool(true))))
            .collect()
    };
    assert_eq!(cmp(Expr::Lt), [true, false, false]);
    assert_eq!(cmp(Expr::Le), [true, true, false]);
    assert_eq!(cmp(Expr::Gt), [false, false, true]);
    assert_eq!(cmp(Expr::Ge), [false, true, true]);
}

#[test]
fn n_ary_arithmetic_edge_cases() {
    assert_eq!(ev(&Expr::Add(vec![])), num(0, 1));
    assert_eq!(ev(&Expr::Mul(vec![])), num(1, 1));
    assert_eq!(ev(&Expr::Add(vec![int(4)])), num(4, 1));
    assert_eq!(ev(&Expr::Mul(vec![int(4)])), num(4, 1));
    assert_eq!(ev(&Expr::Add(vec![int(1), tru()])), None);
    assert_eq!(ev(&Expr::Add(vec![tru(), int(1)])), None);
    assert_eq!(ev(&Expr::Mul(vec![int(2), tru()])), None);
    assert_eq!(ev(&Expr::Mul(vec![tru(), int(2)])), None);
    // unary minus, n-ary minus, empty minus
    assert_eq!(ev(&Expr::Sub(vec![int(5)])), num(-5, 1));
    assert_eq!(ev(&Expr::Sub(vec![int(0)])), num(0, 1));
    assert_eq!(ev(&Expr::Sub(vec![int(10), int(3), int(2)])), num(5, 1));
    assert_eq!(ev(&Expr::Sub(vec![])), None);
    assert_eq!(ev(&Expr::Sub(vec![tru()])), None);
    assert_eq!(ev(&Expr::Sub(vec![tru(), int(1)])), None);
    assert_eq!(ev(&Expr::Sub(vec![int(1), tru()])), None);
    assert_eq!(ev(&Expr::Sub(vec![int(1), int(2), tru()])), None);
}

#[test]
fn division_requires_numbers_and_nonzero_divisor() {
    assert_eq!(ev(&Expr::Div(b(tru()), b(int(1)))), None);
    assert_eq!(ev(&Expr::Div(b(int(1)), b(tru()))), None);
    assert_eq!(ev(&Expr::Div(b(int(1)), b(int(0)))), None);
    assert_eq!(ev(&Expr::Div(b(int(1)), b(int(4)))), num(1, 4));
    // div / mod: Euclidean quotient, non-integers and zero are rejected
    let half = Expr::Real(5, 1);
    let dv = |x: Expr, y: Expr| Expr::IntDiv(b(x), b(y));
    let md = |x: Expr, y: Expr| Expr::IntMod(b(x), b(y));
    assert_eq!(ev(&dv(half.clone(), int(2))), None);
    assert_eq!(ev(&md(half.clone(), int(2))), None);
    assert_eq!(ev(&dv(int(4), half.clone())), None);
    assert_eq!(ev(&md(int(4), half)), None);
    assert_eq!(ev(&dv(int(4), int(0))), None);
    assert_eq!(ev(&md(int(4), int(0))), None);
    assert_eq!(ev(&dv(tru(), int(2))), None);
    assert_eq!(ev(&dv(int(2), tru())), None);
    assert_eq!(ev(&md(tru(), int(2))), None);
    assert_eq!(ev(&md(int(2), tru())), None);
    // an integer-valued real is accepted (4.0 = 4)
    assert_eq!(ev(&dv(Expr::Real(40, 1), int(2))), num(2, 1));
    assert_eq!(ev(&md(Expr::Real(50, 1), int(2))), num(1, 1));
    assert_eq!(ev(&md(int(5), Expr::Real(20, 1))), num(1, 1));
}

#[test]
fn to_int_and_is_int_require_numbers() {
    assert_eq!(ev(&Expr::ToInt(b(tru()))), None);
    assert_eq!(ev(&Expr::IsInt(b(tru()))), None);
    assert_eq!(ev(&Expr::ToInt(b(Expr::Real(-35, 1)))), num(-4, 1));
    assert_eq!(
        ev(&Expr::IsInt(b(Expr::Real(-35, 1)))),
        Some(Value::Bool(false))
    );
    assert_eq!(
        ev(&Expr::IsInt(b(Expr::Real(-30, 1)))),
        Some(Value::Bool(true))
    );
}

#[test]
fn bitvector_ops_reject_wrong_sorts_and_mismatched_widths() {
    let a8 = || bvc(5, 8);
    let c8 = || bvc(3, 8);
    let c9 = || bvc(3, 9);
    type Bin = fn(Box<Expr>, Box<Expr>) -> Expr;
    let bins: [Bin; 18] = [
        |a, c| Expr::BvAdd(a, c),
        |a, c| Expr::BvSub(a, c),
        |a, c| Expr::BvMul(a, c),
        |a, c| Expr::BvAnd(a, c),
        |a, c| Expr::BvOr(a, c),
        |a, c| Expr::BvXor(a, c),
        |a, c| Expr::BvShl(a, c),
        |a, c| Expr::BvLshr(a, c),
        |a, c| Expr::BvAshr(a, c),
        |a, c| Expr::BvUle(a, c),
        |a, c| Expr::BvUlt(a, c),
        |a, c| Expr::BvSle(a, c),
        |a, c| Expr::BvSlt(a, c),
        |a, c| Expr::BvUdiv(a, c),
        |a, c| Expr::BvUrem(a, c),
        |a, c| Expr::BvSdiv(a, c),
        |a, c| Expr::BvSrem(a, c),
        |a, c| Expr::BvSmod(a, c),
    ];
    for (i, f) in bins.iter().enumerate() {
        assert!(
            ev(&f(b(a8()), b(c8()))).is_some(),
            "op {i} works at equal width"
        );
        assert_eq!(ev(&f(b(a8()), b(c9()))), None, "op {i} width mismatch");
        assert_eq!(ev(&f(b(c9()), b(a8()))), None, "op {i} width mismatch");
        assert_eq!(ev(&f(b(int(1)), b(a8()))), None, "op {i} number as bv");
        assert_eq!(ev(&f(b(a8()), b(int(1)))), None, "op {i} number as bv");
        assert_eq!(ev(&f(b(tru()), b(a8()))), None, "op {i} bool as bv");
    }
    // unary / indexed operators
    assert_eq!(ev(&Expr::BvNeg(b(int(1)))), None);
    assert_eq!(ev(&Expr::BvNot(b(int(1)))), None);
    assert_eq!(ev(&Expr::BvZeroExt(2, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvSignExt(2, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvRotl(2, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvRotr(2, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvRepeat(2, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvExtract(1, 0, b(int(1)))), None);
    assert_eq!(ev(&Expr::BvConcat(b(int(1)), b(a8()))), None);
    assert_eq!(ev(&Expr::BvConcat(b(a8()), b(int(1)))), None);
    // bit-vector operands that fail to evaluate propagate None
    let bad = Expr::BvUdiv(b(a8()), b(Expr::Var("z".into(), Type::String)));
    assert_eq!(ev(&Expr::BvAdd(b(bad.clone()), b(a8()))), None);
    assert_eq!(ev(&Expr::BvAdd(b(a8()), b(bad))), None);
}

#[test]
fn extension_repeat_concat_extract_bounds() {
    let max = rz3::theory::bv::MAX_BV_WIDTH;
    // extension: exactly MAX is fine, MAX+1 is refused (also guards against `w - n`)
    for ext in [
        (|n, a| Expr::BvZeroExt(n, a)) as fn(usize, Box<Expr>) -> Expr,
        |n, a| Expr::BvSignExt(n, a),
    ] {
        let w = 100;
        let ok = ev(&ext(max - w, b(zero_bits(w))));
        assert_eq!(ok, Some(Value::Bv(BigUint::zero(), max)));
        assert_eq!(ev(&ext(max - w + 1, b(zero_bits(w)))), None);
        // small widths/extensions: a wrong `w + n` shows up in the width
        assert_eq!(ev(&ext(3, b(bvc(1, 5)))), bv(1, 8));
    }
    // repeat
    assert_eq!(ev(&Expr::BvRepeat(0, b(bvc(1, 4)))), None);
    assert_eq!(ev(&Expr::BvRepeat(3, b(bvc(0b10, 2)))), bv(0b101010, 6));
    assert_eq!(ev(&Expr::BvRepeat(1, b(bvc(0b10, 2)))), bv(0b10, 2));
    let w = 64;
    assert_eq!(
        ev(&Expr::BvRepeat(max / w, b(zero_bits(w)))),
        Some(Value::Bv(BigUint::zero(), max))
    );
    assert_eq!(ev(&Expr::BvRepeat(max / w + 1, b(zero_bits(w)))), None);
    assert_eq!(ev(&Expr::BvRepeat(usize::MAX, b(zero_bits(w)))), None);
    // repeat of a 4096-bit-wide... one copy is fine, two are too many
    assert!(ev(&Expr::BvRepeat(1, b(zero_bits(max)))).is_some());
    assert_eq!(ev(&Expr::BvRepeat(2, b(zero_bits(max)))), None);
    // concat: total width exactly MAX is fine, MAX+1 is refused
    assert_eq!(
        ev(&Expr::BvConcat(b(zero_bits(max - 1)), b(zero_bits(1)))),
        Some(Value::Bv(BigUint::zero(), max))
    );
    assert_eq!(
        ev(&Expr::BvConcat(b(zero_bits(max - 1)), b(zero_bits(2)))),
        None
    );
    assert_eq!(
        ev(&Expr::BvConcat(b(bvc(0b11, 2)), b(bvc(0b1, 1)))),
        bv(0b111, 3)
    );
    assert_eq!(
        ev(&Expr::BvConcat(b(bvc(0b1, 1)), b(bvc(0b01, 2)))),
        bv(0b101, 3)
    );
    // extract: l > h and h >= w are refused, h = w-1 and h = l are fine
    let x = || bvc(0b1011_0110, 8);
    assert_eq!(ev(&Expr::BvExtract(2, 3, b(x()))), None);
    assert_eq!(ev(&Expr::BvExtract(8, 0, b(x()))), None);
    assert_eq!(ev(&Expr::BvExtract(7, 0, b(x()))), bv(0b1011_0110, 8));
    assert_eq!(ev(&Expr::BvExtract(7, 7, b(x()))), bv(1, 1));
    assert_eq!(ev(&Expr::BvExtract(3, 3, b(x()))), bv(0, 1));
    assert_eq!(ev(&Expr::BvExtract(2, 1, b(x()))), bv(0b11, 2));
    assert_eq!(ev(&Expr::BvExtract(6, 2, b(x()))), bv(0b01101, 5));
}

#[test]
fn rotation_amount_reduces_modulo_width() {
    let x = || bvc(0b1001_0110, 8);
    let l = |n| ev(&Expr::BvRotl(n, b(x())));
    let r = |n| ev(&Expr::BvRotr(n, b(x())));
    assert_eq!(l(0), bv(0b1001_0110, 8));
    assert_eq!(l(1), bv(0b0010_1101, 8));
    assert_eq!(l(3), bv(0b1011_0100, 8));
    assert_eq!(l(8), bv(0b1001_0110, 8));
    assert_eq!(l(11), l(3));
    assert_eq!(l(1_000_003), l(3));
    assert_eq!(r(0), bv(0b1001_0110, 8));
    assert_eq!(r(1), bv(0b0100_1011, 8));
    assert_eq!(r(3), bv(0b1101_0010, 8));
    assert_eq!(r(8), bv(0b1001_0110, 8));
    assert_eq!(r(11), r(3));
    // width 1: any rotation is the identity
    assert_eq!(ev(&Expr::BvRotl(5, b(bvc(1, 1)))), bv(1, 1));
    assert_eq!(ev(&Expr::BvRotr(5, b(bvc(0, 1)))), bv(0, 1));
}

#[test]
fn shifts_saturate_at_the_width() {
    let sh = |ctor: fn(Box<Expr>, Box<Expr>) -> Expr, x: u64, y: u64, w: usize| {
        ev(&ctor(b(bvc(x, w)), b(bvc(y, w))))
    };
    let shl: fn(Box<Expr>, Box<Expr>) -> Expr = |a, c| Expr::BvShl(a, c);
    let lshr: fn(Box<Expr>, Box<Expr>) -> Expr = |a, c| Expr::BvLshr(a, c);
    let ashr: fn(Box<Expr>, Box<Expr>) -> Expr = |a, c| Expr::BvAshr(a, c);
    // amount == width is already "all shifted out" (distinguishes >= from >)
    assert_eq!(sh(shl, 0xff, 8, 8), bv(0, 8));
    assert_eq!(sh(lshr, 0xff, 8, 8), bv(0, 8));
    assert_eq!(sh(ashr, 0xff, 8, 8), bv(0xff, 8));
    assert_eq!(sh(ashr, 0x7f, 8, 8), bv(0, 8));
    assert_eq!(sh(ashr, 0x80, 200, 8), bv(0xff, 8));
    assert_eq!(sh(ashr, 0x01, 200, 8), bv(0, 8));
    // lshr/shl never take the arithmetic fill, even with the sign bit set
    assert_eq!(sh(lshr, 0x80, 9, 8), bv(0, 8));
    assert_eq!(sh(shl, 0x80, 9, 8), bv(0, 8));
    // amount == width - 1
    assert_eq!(sh(shl, 0x01, 7, 8), bv(0x80, 8));
    assert_eq!(sh(lshr, 0x80, 7, 8), bv(1, 8));
    assert_eq!(sh(ashr, 0x80, 7, 8), bv(0xff, 8));
    // in-range shifts keep only `w` bits
    assert_eq!(sh(shl, 0xff, 4, 8), bv(0xf0, 8));
    assert_eq!(sh(lshr, 0xff, 4, 8), bv(0x0f, 8));
    assert_eq!(sh(ashr, 0x80, 3, 8), bv(0xf0, 8));
    assert_eq!(sh(ashr, 0x40, 3, 8), bv(0x08, 8));
    // width 1
    assert_eq!(sh(ashr, 1, 1, 1), bv(1, 1));
    assert_eq!(sh(ashr, 0, 1, 1), bv(0, 1));
    assert_eq!(sh(lshr, 1, 1, 1), bv(0, 1));
    assert_eq!(sh(shl, 1, 1, 1), bv(0, 1));
    assert_eq!(sh(shl, 1, 0, 1), bv(1, 1));
    // a shift amount far beyond usize on a wide vector
    let huge = (BigUint::one() << 100u32) - 1u8;
    assert_eq!(
        ev(&Expr::BvShl(
            b(Expr::BvConst(BigUint::one(), 100)),
            b(Expr::BvConst(huge.clone(), 100))
        )),
        bv(0, 100)
    );
    assert_eq!(
        ev(&Expr::BvAshr(
            b(Expr::BvConst(BigUint::one() << 99u32, 100)),
            b(Expr::BvConst(huge.clone(), 100))
        )),
        Some(Value::Bv(huge, 100))
    );
}

#[test]
fn wide_arithmetic_wraps_modulo_2_pow_w() {
    let two100 = BigUint::one() << 100u32;
    let m100 = &two100 - 1u8;
    let bvw = |v: &BigUint| Expr::BvConst(v.clone(), 100);
    let out = |v: BigUint| Some(Value::Bv(v, 100));
    assert_eq!(
        ev(&Expr::BvAdd(b(bvw(&m100)), b(bvw(&BigUint::one())))),
        out(BigUint::zero())
    );
    assert_eq!(
        ev(&Expr::BvSub(
            b(bvw(&BigUint::zero())),
            b(bvw(&BigUint::one()))
        )),
        out(m100.clone())
    );
    assert_eq!(
        ev(&Expr::BvMul(b(bvw(&m100)), b(bvw(&m100)))),
        out(BigUint::one())
    );
    assert_eq!(
        ev(&Expr::BvNeg(b(bvw(&BigUint::zero())))),
        out(BigUint::zero())
    );
    assert_eq!(ev(&Expr::BvNeg(b(bvw(&BigUint::one())))), out(m100.clone()));
    assert_eq!(ev(&Expr::BvNot(b(bvw(&BigUint::zero())))), out(m100));
}

#[test]
fn signed_division_family_reference_values() {
    // 8-bit, operands (x, y) -> (sdiv, srem, smod); every row contrasted with Z3.
    let rows: &[(u64, u64, u64, u64, u64)] = &[
        (7, 2, 3, 1, 1),
        (0xf9, 2, 0xfd, 0xff, 1),
        (7, 0xfe, 0xfd, 1, 0xff),
        (0xf9, 0xfe, 3, 0xff, 0xff),
        (6, 0xfe, 0xfd, 0, 0),
        (0xfa, 2, 0xfd, 0, 0),
        (0x80, 0xff, 0x80, 0, 0),
        (7, 0, 0xff, 7, 7),
        (0xf9, 0, 1, 0xf9, 0xf9),
        (0, 0, 0xff, 0, 0),
    ];
    for &(x, y, sd, sr, sm) in rows {
        let (x, y) = (bvc(x, 8), bvc(y, 8));
        assert_eq!(
            ev(&Expr::BvSdiv(b(x.clone()), b(y.clone()))),
            bv(sd, 8),
            "sdiv"
        );
        assert_eq!(
            ev(&Expr::BvSrem(b(x.clone()), b(y.clone()))),
            bv(sr, 8),
            "srem"
        );
        assert_eq!(ev(&Expr::BvSmod(b(x), b(y))), bv(sm, 8), "smod");
    }
}

#[test]
fn quantifiers_arrays_strings_are_unknown() {
    let arr = Expr::Var(
        "a".into(),
        Type::Array(Box::new(Type::Int), Box::new(Type::Int)),
    );
    assert_eq!(ev(&Expr::Select(b(arr.clone()), b(int(0)))), None);
    assert_eq!(ev(&Expr::Store(b(arr), b(int(0)), b(int(1)))), None);
    assert_eq!(ev(&Expr::StrConst("s".into())), None);
    assert_eq!(ev(&Expr::StrLen(b(Expr::StrConst("s".into())))), None);
    assert_eq!(
        ev(&Expr::ForAll(vec![("i".into(), Type::Int)], b(tru()))),
        None
    );
    assert_eq!(
        ev(&Expr::Exists(vec![("i".into(), Type::Int)], b(tru()))),
        None
    );
    // a quantified conjunct makes the whole assertion Unknown for `holds`
    let f = FunTable::new();
    assert_eq!(
        holds(
            &Expr::And(vec![
                tru(),
                Expr::ForAll(vec![("i".into(), Type::Int)], b(tru()))
            ]),
            &Model::new(),
            &f
        ),
        Verdict::Unknown
    );
}

#[test]
fn uninterpreted_functions_use_the_table() {
    let app = |n: &str, args: Vec<Expr>| Expr::App(n.into(), args);
    let n = |i: i64| Value::Num(BigRational::from_integer(i.into()));
    let mut t = FunTable::new();
    t.insert(
        "f".into(),
        vec![
            (vec![n(1)], n(10)),
            (vec![n(2)], n(20)),
            (vec![n(1), n(2)], n(12)),
        ],
    );
    t.insert("g".into(), vec![(vec![], Value::Bool(true))]);
    let m = Model::new();
    assert_eq!(eval_with(&app("f", vec![int(1)]), &m, &t), num(10, 1));
    assert_eq!(eval_with(&app("f", vec![int(2)]), &m, &t), num(20, 1));
    assert_eq!(
        eval_with(&app("f", vec![int(1), int(2)]), &m, &t),
        num(12, 1)
    );
    // argument not in the table / wrong arity / unknown function / unevaluable argument
    assert_eq!(eval_with(&app("f", vec![int(3)]), &m, &t), None);
    assert_eq!(eval_with(&app("f", vec![int(2), int(1)]), &m, &t), None);
    assert_eq!(eval_with(&app("h", vec![int(1)]), &m, &t), None);
    assert_eq!(
        eval_with(&app("f", vec![Expr::IntDiv(b(int(1)), b(int(0)))]), &m, &t),
        None
    );
    assert_eq!(
        eval_with(&app("g", vec![]), &m, &t),
        Some(Value::Bool(true))
    );
    // arguments are evaluated first, so computed arguments find their entry
    let arg = Expr::Add(vec![int(1), int(1)]);
    assert_eq!(eval_with(&app("f", vec![arg]), &m, &t), num(20, 1));
    // arguments may be variables resolved through the model
    let mut m2 = Model::new();
    m2.insert("v".into(), ModelValue::Int(1.into()));
    let v = Expr::Var("v".into(), Type::Int);
    assert_eq!(eval_with(&app("f", vec![v]), &m2, &t), num(10, 1));
    // without a table nothing is interpreted
    assert_eq!(eval(&app("f", vec![int(1)]), &m), None);
    // results feed into enclosing terms
    let sum = Expr::Add(vec![app("f", vec![int(1)]), app("f", vec![int(2)])]);
    assert_eq!(eval_with(&sum, &m, &t), num(30, 1));
    // a Boolean-valued application is usable as a formula
    assert_eq!(holds(&app("g", vec![]), &m, &t), Verdict::True);
}

#[test]
fn holds_verdicts() {
    let f = FunTable::new();
    let m = Model::new();
    assert_eq!(holds(&tru(), &m, &f), Verdict::True);
    assert_eq!(holds(&Expr::Bool(false), &m, &f), Verdict::False);
    assert_eq!(
        holds(&Expr::Lt(b(int(2)), b(int(1))), &m, &f),
        Verdict::False
    );
    assert_eq!(
        holds(&Expr::Lt(b(int(1)), b(int(2))), &m, &f),
        Verdict::True
    );
    // a value that is not Boolean, and something not interpreted, are both Unknown
    assert_eq!(holds(&int(1), &m, &f), Verdict::Unknown);
    assert_eq!(holds(&bvc(1, 1), &m, &f), Verdict::Unknown);
    assert_eq!(
        holds(
            &Expr::Eq(b(int(1)), b(Expr::IntDiv(b(int(1)), b(int(0))))),
            &m,
            &f
        ),
        Verdict::Unknown
    );
}
