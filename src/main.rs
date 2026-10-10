use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use rz3::ast::fp::{FloatValue, RoundingMode};
use rz3::ast::{Expr, ModelValue, Type};
use rz3::parser::{Command, Parser};
use rz3::Rz3Solver;
use rz3::SolverResult;
use std::env;
use std::fs;

/// Real benchmarks nest terms thousands of levels deep and every pass over them is
/// recursive, so the work runs on a thread with a large stack instead of the 8 MiB main one.
fn main() {
    let worker = std::thread::Builder::new()
        .stack_size(2 << 30)
        .spawn(real_main)
        .expect("failed to start the solver thread");
    if worker.join().is_err() {
        std::process::exit(101);
    }
}

fn real_main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: rz3 <file.smt2>");
        return;
    }

    let input = match fs::read_to_string(&args[1]) {
        Ok(input) => input,
        Err(err) => {
            eprintln!("failed to read {}: {}", args[1], err);
            std::process::exit(1);
        }
    };
    let mut parser = Parser::strict(&input);
    let mut solver = Rz3Solver::new();
    if let Some(ms) = env::var("RZ3_DEADLINE_MS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        solver.set_time_limit(std::time::Duration::from_millis(ms));
    }

    let mut printed_check_sat = false;
    let mut last_result = None;
    while let Some(command) = parser.parse_command() {
        if parser.error().is_some() {
            break;
        }
        match command {
            Command::SetLogic(_) | Command::SetOption(_, _) | Command::SetInfo(_, _) => {}
            Command::DeclareFun(name, params, return_type) => {
                solver.declare_fun_signature(name, params, return_type);
            }
            // The parser expands `define-fun` bodies at every use site; declaring the
            // name here as an uninterpreted function would silently drop the body.
            Command::DefineFun(_, _, _, _) | Command::Skipped(_) | Command::DeclareSort(_) => {}
            Command::Assert(expr) => solver.assert(&expr),
            Command::Push(n) => {
                for _ in 0..n {
                    solver.push();
                }
            }
            Command::Pop(n) => {
                for _ in 0..n {
                    solver.pop();
                }
            }
            Command::CheckSat => {
                let result = solver.check();
                print_result(result);
                last_result = Some(result);
                printed_check_sat = true;
            }
            Command::GetModel => {
                if ensure_sat(&mut solver, &mut last_result, &mut printed_check_sat) {
                    print_model(&solver.get_model());
                }
            }
            Command::GetValue(exprs) => {
                if ensure_sat(&mut solver, &mut last_result, &mut printed_check_sat) {
                    print_values(&solver, &exprs);
                }
            }
            Command::Exit => break,
        }
    }

    if let Some(err) = parser.error() {
        // Fail closed: a parse failure must never be followed by a verdict computed
        // from a truncated or weakened formula.
        println!("(error \"{}\")", err.replace('"', "\"\""));
        std::process::exit(1);
    }

    if !printed_check_sat {
        print_result(solver.check());
    }
    print_stats(&solver);
}

/// Phase breakdown on stderr when `RZ3_STATS` is set (never mixed into the answer).
fn print_stats(solver: &Rz3Solver) {
    if env::var_os("RZ3_STATS").is_none() {
        return;
    }
    let st = solver.stats();
    let ms = |ns: u128| ns as f64 / 1e6;
    eprintln!(
        "stats: assert_ms={:.1} sat_ms={:.1} theory_ms={:.1} certify_ms={:.1} check_calls={} dpll_iterations={} theory_conflicts={} branches={} pivots={} atoms={} sat_vars={}",
        ms(st.assert_ns),
        ms(st.sat_ns),
        ms(st.theory_ns),
        ms(st.certify_ns),
        st.check_calls,
        st.dpll_iterations,
        st.theory_conflicts,
        st.branches,
        st.pivots,
        st.atoms,
        st.sat_vars
    );
    eprintln!(
        "stats: array_instances={} sat_propagations={} sat_decisions={} sat_conflicts={} sat_restarts={} learned={}",
        st.array_instances,
        st.sat.propagations,
        st.sat.decisions,
        st.sat.conflicts,
        st.sat.restarts,
        st.sat.learned_clauses
    );
    eprintln!(
        "stats: lin_ms={:.1} dl_ms={:.1} (repair {:.1}, search {:.1}) dl_propagations={}",
        ms(st.lin_ns),
        ms(st.dl_ns),
        ms(st.dl_repair_ns),
        ms(st.dl_search_ns),
        st.dl_propagations
    );
    if let Some(why) = st.unknown_reason {
        eprintln!("stats: unknown_reason={why}");
    }
}

fn ensure_sat(
    solver: &mut Rz3Solver,
    last_result: &mut Option<SolverResult>,
    printed_check_sat: &mut bool,
) -> bool {
    if last_result.is_none() {
        let result = solver.check();
        print_result(result);
        *last_result = Some(result);
        *printed_check_sat = true;
    }
    matches!(*last_result, Some(SolverResult::Sat))
}

fn print_result(result: SolverResult) {
    match result {
        SolverResult::Sat => println!("sat"),
        SolverResult::Unsat => println!("unsat"),
        SolverResult::Unknown => println!("unknown"),
    }
}

fn print_model(model: &std::collections::BTreeMap<String, ModelValue>) {
    println!("(");
    for (name, value) in model {
        println!(
            "  (define-fun {} () {} {})",
            name,
            format_model_sort(value),
            format_model_value(value)
        );
    }
    println!(")");
}

fn print_values(solver: &Rz3Solver, exprs: &[Expr]) {
    let mut parts = Vec::new();
    for expr in exprs {
        if let Some(value) = solver.get_value(expr) {
            parts.push(format!(
                "({} {})",
                format_expr(expr),
                format_model_value(&value)
            ));
        }
    }
    println!("({})", parts.join(" "));
}

fn format_model_sort(value: &ModelValue) -> String {
    match value {
        ModelValue::Bool(_) => "Bool".to_string(),
        ModelValue::Int(_) => "Int".to_string(),
        ModelValue::Real(_) => "Real".to_string(),
        ModelValue::BitVec(_, width) => format!("(_ BitVec {})", width),
        ModelValue::Float(value) => format!(
            "(_ FloatingPoint {} {})",
            value.sort.exponent_bits, value.sort.significand_bits
        ),
    }
}

fn format_model_value(value: &ModelValue) -> String {
    match value {
        ModelValue::Bool(value) => value.to_string(),
        ModelValue::Int(value) => format_integer(value),
        ModelValue::Real(value) => format_rational(value),
        ModelValue::BitVec(value, width) => format_bits(value, *width),
        ModelValue::Float(value) => format_float(value),
    }
}

/// SMT-LIB real constants: non-negative decimals, `(/ n.0 d.0)` for fractions, and
/// `(- t)` for negatives (a negative numeral literal is not standard syntax).
fn format_rational(value: &BigRational) -> String {
    use num_traits::Signed;
    let abs = value.abs();
    let body = if abs.denom() == &BigInt::from(1) {
        format!("{}.0", abs.numer())
    } else {
        format!("(/ {}.0 {}.0)", abs.numer(), abs.denom())
    };
    if value.is_negative() {
        format!("(- {body})")
    } else {
        body
    }
}

fn format_integer(value: &BigInt) -> String {
    use num_traits::Signed;
    if value.is_negative() {
        format!("(- {})", value.abs())
    } else {
        value.to_string()
    }
}

fn format_float(value: &FloatValue) -> String {
    let fraction_bits = usize::from(value.sort.significand_bits.saturating_sub(1));
    let exponent_bits = usize::from(value.sort.exponent_bits);
    let total_bits = 1 + exponent_bits + fraction_bits;
    let bits = format_biguint_bits(&value.to_bits(RoundingMode::NearestTiesToEven), total_bits);
    if bits.len() != total_bits {
        return format!("#b{}", bits);
    }
    let sign = &bits[0..1];
    let exponent = &bits[1..1 + exponent_bits];
    let significand = &bits[1 + exponent_bits..];
    format!("(fp #b{} #b{} #b{})", sign, exponent, significand)
}

fn format_biguint_bits(value: &BigUint, width: usize) -> String {
    let raw = value.to_str_radix(2);
    if raw.len() >= width {
        raw
    } else {
        format!("{}{}", "0".repeat(width - raw.len()), raw)
    }
}

fn format_expr(expr: &Expr) -> String {
    match expr {
        Expr::Bool(value) => value.to_string(),
        Expr::Int(value) => value.to_string(),
        Expr::Real(value, scale) => format_decimal(*value, *scale),
        Expr::Var(name, _) => name.clone(),
        Expr::BvConst(value, width) => format_bits(value, *width),
        Expr::App(name, args) => {
            let rendered = args.iter().map(format_expr).collect::<Vec<_>>().join(" ");
            format!("({} {})", name, rendered)
        }
        Expr::Eq(a, b) => format!("(= {} {})", format_expr(a), format_expr(b)),
        Expr::Not(inner) => format!("(not {})", format_expr(inner)),
        Expr::And(args) => format_nary("and", args),
        Expr::Or(args) => format_nary("or", args),
        Expr::Add(args) => format_nary("+", args),
        Expr::Sub(args) => format_nary("-", args),
        Expr::Mul(args) => format_nary("*", args),
        Expr::Div(a, b) => format!("(/ {} {})", format_expr(a), format_expr(b)),
        Expr::Lt(a, b) => format!("(< {} {})", format_expr(a), format_expr(b)),
        Expr::Le(a, b) => format!("(<= {} {})", format_expr(a), format_expr(b)),
        Expr::Gt(a, b) => format!("(> {} {})", format_expr(a), format_expr(b)),
        Expr::Ge(a, b) => format!("(>= {} {})", format_expr(a), format_expr(b)),
        Expr::Ite(c, t, e) => format!(
            "(ite {} {} {})",
            format_expr(c),
            format_expr(t),
            format_expr(e)
        ),
        Expr::BvAdd(a, b) => format!("(bvadd {} {})", format_expr(a), format_expr(b)),
        Expr::BvSub(a, b) => format!("(bvsub {} {})", format_expr(a), format_expr(b)),
        Expr::BvMul(a, b) => format!("(bvmul {} {})", format_expr(a), format_expr(b)),
        Expr::BvAnd(a, b) => format!("(bvand {} {})", format_expr(a), format_expr(b)),
        Expr::BvOr(a, b) => format!("(bvor {} {})", format_expr(a), format_expr(b)),
        Expr::BvXor(a, b) => format!("(bvxor {} {})", format_expr(a), format_expr(b)),
        Expr::BvNot(inner) => format!("(bvnot {})", format_expr(inner)),
        Expr::BvExtract(high, low, inner) => {
            format!("((_ extract {} {}) {})", high, low, format_expr(inner))
        }
        Expr::Select(array, index) => {
            format!("(select {} {})", format_expr(array), format_expr(index))
        }
        Expr::Store(array, index, value) => format!(
            "(store {} {} {})",
            format_expr(array),
            format_expr(index),
            format_expr(value)
        ),
        Expr::StrConst(value) => format!("\"{}\"", value),
        Expr::StrConcat(args) => format_nary("str.++", args),
        Expr::StrLen(inner) => format!("(str.len {})", format_expr(inner)),
        Expr::StrContains(a, b) => format!("(str.contains {} {})", format_expr(a), format_expr(b)),
        Expr::ForAll(vars, body) => format_quantifier("forall", vars, body),
        Expr::Exists(vars, body) => format_quantifier("exists", vars, body),
        Expr::BigRat(num, den) => match num.strip_prefix('-') {
            Some(abs) => format!("(- (/ {abs}.0 {den}.0))"),
            None => format!("(/ {num}.0 {den}.0)"),
        },
        Expr::Implies(a, b) => format!("(=> {} {})", format_expr(a), format_expr(b)),
        Expr::IntDiv(a, b) => format!("(div {} {})", format_expr(a), format_expr(b)),
        Expr::IntMod(a, b) => format!("(mod {} {})", format_expr(a), format_expr(b)),
        Expr::ToInt(a) => format!("(to_int {})", format_expr(a)),
        Expr::IsInt(a) => format!("(is_int {})", format_expr(a)),
        Expr::BvNeg(a) => format!("(bvneg {})", format_expr(a)),
        Expr::BvUdiv(a, b) => format!("(bvudiv {} {})", format_expr(a), format_expr(b)),
        Expr::BvUrem(a, b) => format!("(bvurem {} {})", format_expr(a), format_expr(b)),
        Expr::BvSdiv(a, b) => format!("(bvsdiv {} {})", format_expr(a), format_expr(b)),
        Expr::BvSrem(a, b) => format!("(bvsrem {} {})", format_expr(a), format_expr(b)),
        Expr::BvSmod(a, b) => format!("(bvsmod {} {})", format_expr(a), format_expr(b)),
        Expr::BvShl(a, b) => format!("(bvshl {} {})", format_expr(a), format_expr(b)),
        Expr::BvLshr(a, b) => format!("(bvlshr {} {})", format_expr(a), format_expr(b)),
        Expr::BvAshr(a, b) => format!("(bvashr {} {})", format_expr(a), format_expr(b)),
        Expr::BvUle(a, b) => format!("(bvule {} {})", format_expr(a), format_expr(b)),
        Expr::BvUlt(a, b) => format!("(bvult {} {})", format_expr(a), format_expr(b)),
        Expr::BvSle(a, b) => format!("(bvsle {} {})", format_expr(a), format_expr(b)),
        Expr::BvSlt(a, b) => format!("(bvslt {} {})", format_expr(a), format_expr(b)),
        Expr::BvConcat(a, b) => format!("(concat {} {})", format_expr(a), format_expr(b)),
        Expr::BvZeroExt(n, a) => format!("((_ zero_extend {n}) {})", format_expr(a)),
        Expr::BvSignExt(n, a) => format!("((_ sign_extend {n}) {})", format_expr(a)),
        Expr::BvRotl(n, a) => format!("((_ rotate_left {n}) {})", format_expr(a)),
        Expr::BvRotr(n, a) => format!("((_ rotate_right {n}) {})", format_expr(a)),
        Expr::BvRepeat(n, a) => format!("((_ repeat {n}) {})", format_expr(a)),
        Expr::ConstArray(ty, v) => format!("((as const {}) {})", format_type(ty), format_expr(v)),
        #[allow(unreachable_patterns)]
        _ => expr.to_string(),
    }
}

fn format_nary(op: &str, args: &[Expr]) -> String {
    let rendered = args.iter().map(format_expr).collect::<Vec<_>>().join(" ");
    format!("({} {})", op, rendered)
}

fn format_quantifier(op: &str, vars: &[(String, Type)], body: &Expr) -> String {
    let rendered_vars = vars
        .iter()
        .map(|(name, ty)| format!("({} {})", name, format_type(ty)))
        .collect::<Vec<_>>()
        .join(" ");
    format!("({} ({}) {})", op, rendered_vars, format_expr(body))
}

fn format_type(ty: &Type) -> String {
    match ty {
        Type::Unknown => "Unknown".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Int => "Int".to_string(),
        Type::Real => "Real".to_string(),
        Type::Float(sort) => format!(
            "(_ FloatingPoint {} {})",
            sort.exponent_bits, sort.significand_bits
        ),
        Type::BitVec(width) => format!("(_ BitVec {})", width),
        Type::String => "String".to_string(),
        Type::Sort(name) => name.clone(),
        Type::Array(index, value) => {
            format!("(Array {} {})", format_type(index), format_type(value))
        }
        Type::Fn(args, ret) => {
            let rendered = args.iter().map(format_type).collect::<Vec<_>>().join(" ");
            format!("(-> {} {})", rendered, format_type(ret))
        }
    }
}

fn format_decimal(value: i64, scale: u32) -> String {
    if scale == 0 {
        return value.to_string();
    }
    let negative = value.is_negative();
    let digits = value.unsigned_abs().to_string();
    let scale = scale as usize;
    let rendered = if digits.len() <= scale {
        format!("0.{}{}", "0".repeat(scale - digits.len()), digits)
    } else {
        let split = digits.len() - scale;
        format!("{}.{}", &digits[..split], &digits[split..])
    };
    if negative {
        format!("-{}", rendered)
    } else {
        rendered
    }
}

/// `#b...` literal of exactly `width` digits for an arbitrary-precision value.
fn format_bits(value: &num_bigint::BigUint, width: usize) -> String {
    let digits = value.to_str_radix(2);
    let digits = if value == &num_bigint::BigUint::from(0u8) {
        String::new()
    } else {
        digits
    };
    format!(
        "#b{}{}",
        "0".repeat(width.saturating_sub(digits.len())),
        digits
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rz3::ast::fp::{FloatClass, FloatSort, FloatValue};

    fn b(e: Expr) -> Box<Expr> {
        Box::new(e)
    }
    fn x() -> Expr {
        Expr::Var("x".to_string(), Type::Int)
    }
    fn bits(v: u64, w: usize) -> Expr {
        Expr::BvConst(BigUint::from(v), w)
    }
    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }
    fn fp(e: u16, s: u16, class: FloatClass) -> FloatValue {
        FloatValue {
            sort: FloatSort {
                exponent_bits: e,
                significand_bits: s,
            },
            class,
        }
    }

    #[test]
    fn rational_formatting() {
        assert_eq!(format_rational(&rat(0, 1)), "0.0");
        assert_eq!(format_rational(&rat(3, 1)), "3.0");
        assert_eq!(format_rational(&rat(-3, 1)), "(- 3.0)");
        assert_eq!(format_rational(&rat(1, 2)), "(/ 1.0 2.0)");
        assert_eq!(format_rational(&rat(-1, 2)), "(- (/ 1.0 2.0))");
        assert_eq!(format_rational(&rat(14, 4)), "(/ 7.0 2.0)");
        assert_eq!(format_rational(&rat(-7, 3)), "(- (/ 7.0 3.0))");
        assert_eq!(format_rational(&rat(10, 1)), "10.0");
    }

    #[test]
    fn integer_formatting() {
        assert_eq!(format_integer(&BigInt::from(0)), "0");
        assert_eq!(format_integer(&BigInt::from(5)), "5");
        assert_eq!(format_integer(&BigInt::from(-5)), "(- 5)");
        let big: BigInt = "-123456789012345678901234567890".parse().unwrap();
        assert_eq!(format_integer(&big), "(- 123456789012345678901234567890)");
    }

    #[test]
    fn bit_pattern_formatting() {
        let v = |n: u64| BigUint::from(n);
        assert_eq!(format_bits(&v(0), 4), "#b0000");
        assert_eq!(format_bits(&v(0), 1), "#b0");
        assert_eq!(format_bits(&v(1), 1), "#b1");
        assert_eq!(format_bits(&v(5), 4), "#b0101");
        assert_eq!(format_bits(&v(15), 4), "#b1111");
        assert_eq!(format_bits(&v(5), 8), "#b00000101");
        // a pattern wider than the declared width is printed in full, never truncated
        assert_eq!(format_bits(&v(5), 2), "#b101");
        let wide = BigUint::from(1u8) << 99u32;
        assert_eq!(format_bits(&wide, 100), format!("#b1{}", "0".repeat(99)));
        assert_eq!(format_biguint_bits(&v(5), 8), "00000101");
        assert_eq!(format_biguint_bits(&v(5), 3), "101");
        assert_eq!(format_biguint_bits(&v(5), 2), "101");
        assert_eq!(format_biguint_bits(&v(0), 1), "0");
        assert_eq!(format_biguint_bits(&v(0), 3), "000");
    }

    #[test]
    fn decimal_formatting() {
        assert_eq!(format_decimal(0, 0), "0");
        assert_eq!(format_decimal(5, 0), "5");
        assert_eq!(format_decimal(-5, 0), "-5");
        assert_eq!(format_decimal(25, 1), "2.5");
        assert_eq!(format_decimal(-25, 1), "-2.5");
        assert_eq!(format_decimal(5, 1), "0.5");
        assert_eq!(format_decimal(-5, 1), "-0.5");
        assert_eq!(format_decimal(25, 2), "0.25");
        assert_eq!(format_decimal(-25, 2), "-0.25");
        assert_eq!(format_decimal(5, 3), "0.005");
        assert_eq!(format_decimal(12345, 2), "123.45");
        assert_eq!(format_decimal(100, 2), "1.00");
        assert_eq!(format_decimal(1000, 2), "10.00");
        assert_eq!(format_decimal(0, 2), "0.00");
        assert_eq!(format_decimal(i64::MIN, 0), "-9223372036854775808");
        assert_eq!(format_decimal(i64::MIN, 2), "-92233720368547758.08");
    }

    #[test]
    fn float_formatting() {
        let one_and_half = FloatClass::Finite {
            negative: false,
            value: rat(3, 2),
        };
        assert_eq!(
            format_float(&fp(8, 24, one_and_half)),
            "(fp #b0 #b01111111 #b10000000000000000000000)"
        );
        let neg = FloatClass::Finite {
            negative: true,
            value: rat(3, 4),
        };
        assert_eq!(
            format_float(&fp(5, 11, neg)),
            "(fp #b1 #b01110 #b1000000000)"
        );
        assert_eq!(
            format_float(&fp(8, 24, FloatClass::PositiveZero)),
            "(fp #b0 #b00000000 #b00000000000000000000000)"
        );
        assert_eq!(
            format_float(&fp(8, 24, FloatClass::NegativeZero)),
            "(fp #b1 #b00000000 #b00000000000000000000000)"
        );
        assert_eq!(
            format_float(&fp(8, 24, FloatClass::PositiveInfinity)),
            "(fp #b0 #b11111111 #b00000000000000000000000)"
        );
        assert_eq!(
            format_float(&fp(5, 11, FloatClass::NegativeInfinity)),
            "(fp #b1 #b11111 #b0000000000)"
        );
        // the three fields together always span 1 + exponent + (significand - 1) bits
        let v = format_float(&fp(11, 53, FloatClass::PositiveZero));
        assert_eq!(v.len(), "(fp #b0 #b #b)".len() + 11 + 52);
    }

    #[test]
    fn model_sorts_and_values() {
        let z = |n: i64| ModelValue::Int(BigInt::from(n));
        assert_eq!(format_model_sort(&ModelValue::Bool(true)), "Bool");
        assert_eq!(format_model_sort(&z(1)), "Int");
        assert_eq!(format_model_sort(&ModelValue::Real(rat(1, 2))), "Real");
        assert_eq!(
            format_model_sort(&ModelValue::BitVec(BigUint::from(1u8), 12)),
            "(_ BitVec 12)"
        );
        let f = ModelValue::Float(fp(8, 24, FloatClass::PositiveZero));
        assert_eq!(format_model_sort(&f), "(_ FloatingPoint 8 24)");
        assert_eq!(format_model_value(&ModelValue::Bool(true)), "true");
        assert_eq!(format_model_value(&ModelValue::Bool(false)), "false");
        assert_eq!(format_model_value(&z(-3)), "(- 3)");
        assert_eq!(format_model_value(&z(3)), "3");
        assert_eq!(
            format_model_value(&ModelValue::Real(rat(-3, 2))),
            "(- (/ 3.0 2.0))"
        );
        assert_eq!(
            format_model_value(&ModelValue::BitVec(BigUint::from(5u8), 4)),
            "#b0101"
        );
        assert_eq!(
            format_model_value(&f),
            "(fp #b0 #b00000000 #b00000000000000000000000)"
        );
    }

    #[test]
    fn type_formatting() {
        let arr = Type::Array(b_ty(Type::Int), b_ty(Type::BitVec(8)));
        assert_eq!(format_type(&Type::Unknown), "Unknown");
        assert_eq!(format_type(&Type::Bool), "Bool");
        assert_eq!(format_type(&Type::Int), "Int");
        assert_eq!(format_type(&Type::Real), "Real");
        assert_eq!(format_type(&Type::String), "String");
        assert_eq!(format_type(&Type::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(format_type(&Type::Sort("U".to_string())), "U");
        assert_eq!(
            format_type(&Type::Float(FloatSort {
                exponent_bits: 11,
                significand_bits: 53
            })),
            "(_ FloatingPoint 11 53)"
        );
        assert_eq!(format_type(&arr), "(Array Int (_ BitVec 8))");
        assert_eq!(
            format_type(&Type::Fn(vec![Type::Int, Type::Bool], b_ty(Type::Real))),
            "(-> Int Bool Real)"
        );
    }

    fn b_ty(t: Type) -> Box<Type> {
        Box::new(t)
    }

    #[test]
    fn expression_echo_for_every_supported_term() {
        let y = || Expr::Var("y".to_string(), Type::Int);
        let p = || Expr::Var("p".to_string(), Type::Bool);
        let v = || Expr::Var("v".to_string(), Type::BitVec(8));
        let cases: Vec<(Expr, &str)> = vec![
            (Expr::Bool(true), "true"),
            (Expr::Bool(false), "false"),
            (Expr::Int(-3), "-3"),
            (Expr::Int(12), "12"),
            (Expr::Real(25, 1), "2.5"),
            (Expr::Real(-5, 2), "-0.05"),
            (x(), "x"),
            (bits(5, 4), "#b0101"),
            (Expr::App("f".into(), vec![Expr::Int(1), x()]), "(f 1 x)"),
            (Expr::Eq(b(x()), b(y())), "(= x y)"),
            (Expr::Not(b(p())), "(not p)"),
            (Expr::And(vec![p(), p(), p()]), "(and p p p)"),
            (Expr::Or(vec![p(), p()]), "(or p p)"),
            (Expr::Add(vec![x(), y(), Expr::Int(1)]), "(+ x y 1)"),
            (Expr::Sub(vec![x(), y()]), "(- x y)"),
            (Expr::Mul(vec![x(), y()]), "(* x y)"),
            (Expr::Div(b(x()), b(y())), "(/ x y)"),
            (Expr::Lt(b(x()), b(y())), "(< x y)"),
            (Expr::Le(b(x()), b(y())), "(<= x y)"),
            (Expr::Gt(b(x()), b(y())), "(> x y)"),
            (Expr::Ge(b(x()), b(y())), "(>= x y)"),
            (Expr::Ite(b(p()), b(x()), b(y())), "(ite p x y)"),
            (Expr::BvAdd(b(v()), b(v())), "(bvadd v v)"),
            (Expr::BvSub(b(v()), b(v())), "(bvsub v v)"),
            (Expr::BvMul(b(v()), b(v())), "(bvmul v v)"),
            (Expr::BvAnd(b(v()), b(v())), "(bvand v v)"),
            (Expr::BvOr(b(v()), b(v())), "(bvor v v)"),
            (Expr::BvXor(b(v()), b(v())), "(bvxor v v)"),
            (Expr::BvNot(b(v())), "(bvnot v)"),
            (Expr::BvExtract(7, 4, b(v())), "((_ extract 7 4) v)"),
            (
                Expr::Select(b(Expr::Var("a".into(), Type::Int)), b(Expr::Int(1))),
                "(select a 1)",
            ),
            (
                Expr::Store(
                    b(Expr::Var("a".into(), Type::Int)),
                    b(Expr::Int(1)),
                    b(Expr::Int(2)),
                ),
                "(store a 1 2)",
            ),
            (Expr::StrConst("ab".into()), "\"ab\""),
            (
                Expr::StrConcat(vec![Expr::StrConst("a".into()), Expr::StrConst("b".into())]),
                "(str.++ \"a\" \"b\")",
            ),
            (
                Expr::StrLen(b(Expr::StrConst("a".into()))),
                "(str.len \"a\")",
            ),
            (
                Expr::StrContains(
                    b(Expr::StrConst("ab".into())),
                    b(Expr::StrConst("a".into())),
                ),
                "(str.contains \"ab\" \"a\")",
            ),
            (
                Expr::ForAll(
                    vec![("i".into(), Type::Int), ("w".into(), Type::BitVec(8))],
                    b(Expr::Gt(
                        b(Expr::Var("i".into(), Type::Int)),
                        b(Expr::Int(0)),
                    )),
                ),
                "(forall ((i Int) (w (_ BitVec 8))) (> i 0))",
            ),
            (
                Expr::Exists(vec![("r".into(), Type::Real)], b(Expr::Bool(true))),
                "(exists ((r Real)) true)",
            ),
        ];
        for (e, want) in cases {
            assert_eq!(format_expr(&e), want);
        }
        // nesting recurses through the same printer
        let nested = Expr::Not(b(Expr::Eq(b(Expr::Add(vec![x(), Expr::Int(1)])), b(y()))));
        assert_eq!(format_expr(&nested), "(not (= (+ x 1) y))");
        assert_eq!(format_nary("and", &[]), "(and )");
        assert_eq!(format_nary("+", &[Expr::Int(1), Expr::Int(2)]), "(+ 1 2)");
        assert_eq!(
            format_quantifier("forall", &[("a".into(), Type::Bool)], &Expr::Bool(true)),
            "(forall ((a Bool)) true)"
        );
    }
}
