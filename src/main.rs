use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use rz3::ast::fp::{FloatValue, RoundingMode};
use rz3::ast::{Expr, ModelValue, Type};
use rz3::parser::{Command, Parser};
use rz3::Rz3Solver;
use rz3::SolverResult;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: rz3 <file.smt2>");
        return;
    }

    let input = match fs::read_to_string(&args[1]) {
        Ok(input) => input,
        Err(err) => {
            eprintln!("failed to read {}: {}", args[1], err);
            return;
        }
    };
    let mut parser = Parser::new(&input);
    let mut solver = Rz3Solver::new();

    let mut printed_check_sat = false;
    let mut last_result = None;
    while let Some(command) = parser.parse_command() {
        match command {
            Command::SetLogic(_) | Command::SetOption(_, _) | Command::SetInfo(_, _) => {}
            Command::DeclareFun(name, params, return_type) => {
                solver.declare_fun_signature(name, params, return_type);
            }
            Command::DefineFun(name, params, return_type, _) => {
                let param_types = params.into_iter().map(|(_, ty)| ty).collect();
                solver.declare_fun_signature(name, param_types, return_type);
            }
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

    if !printed_check_sat {
        print_result(solver.check());
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
        ModelValue::Int(value) => value.to_string(),
        ModelValue::Real(value) => format_rational(value),
        ModelValue::BitVec(value, width) => format!("#b{:0width$b}", value, width = *width),
        ModelValue::Float(value) => format_float(value),
    }
}

fn format_rational(value: &BigRational) -> String {
    if value.denom() == &BigInt::from(1) {
        value.numer().to_string()
    } else {
        format!("(/ {} {})", value.numer(), value.denom())
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
        Expr::BvConst(value, width) => format!("#b{:0width$b}", value, width = *width),
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
