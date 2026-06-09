use num_bigint::BigInt;
use num_rational::BigRational;
use rz3::ast::{fp::FloatSort, Expr, ModelValue, Type};
use rz3::parser::{Command, Parser};
use rz3::{Rz3Solver, SolverResult};

fn fp32(sign: u64, exp: u64, sig: u64) -> Expr {
    Expr::App(
        "fp".to_string(),
        vec![
            Expr::BvConst(sign, 1),
            Expr::BvConst(exp, 8),
            Expr::BvConst(sig, 23),
        ],
    )
}

#[test]
fn parser_preserves_get_value_expressions() {
    let mut parser = Parser::new("(get-value (x #b00000101))");
    let exprs = match parser.parse_command() {
        Some(Command::GetValue(exprs)) => exprs,
        other => {
            assert!(
                matches!(other, Some(Command::GetValue(_))),
                "expected Command::GetValue"
            );
            return;
        }
    };

    assert_eq!(exprs.len(), 2);
    assert!(matches!(&exprs[0], Expr::Var(name, _) if name == "x"));
    assert!(matches!(exprs[1], Expr::BvConst(5, 8)));
}

#[test]
fn get_value_returns_exact_lra_rational_model_value() {
    let x = Expr::Var("x".to_string(), Type::Real);
    let mut solver = Rz3Solver::new();
    solver.declare_fun("x".to_string(), Type::Real);
    solver.assert(&Expr::Eq(Box::new(x.clone()), Box::new(Expr::Real(125, 2))));

    assert!(matches!(solver.check(), SolverResult::Sat));
    let value = match solver.get_value(&x) {
        Some(value) => value,
        None => {
            assert!(
                solver.get_value(&x).is_some(),
                "expected exact model value for x"
            );
            return;
        }
    };

    assert!(matches!(
        value,
        ModelValue::Real(r) if r == BigRational::new(BigInt::from(125), BigInt::from(100))
    ));
}

#[test]
fn get_value_handles_large_decimal_scale_without_i64_overflow() {
    let x = Expr::Var("tiny".to_string(), Type::Real);
    let mut solver = Rz3Solver::new();
    solver.declare_fun("tiny".to_string(), Type::Real);
    solver.assert(&Expr::Eq(Box::new(x.clone()), Box::new(Expr::Real(1, 30))));

    assert!(matches!(solver.check(), SolverResult::Sat));
    let value = match solver.get_value(&x) {
        Some(value) => value,
        None => {
            assert!(solver.get_value(&x).is_some(), "expected exact model value for tiny");
            return;
        }
    };

    assert!(matches!(
        value,
        ModelValue::Real(r) if r == BigRational::new(BigInt::from(1), BigInt::from(10u8).pow(30))
    ));
}

#[test]
fn get_value_returns_exact_ground_fp_value() {
    let one = fp32(0, 0x7f, 0);
    let solver = Rz3Solver::new();
    let value = match solver.get_value(&one) {
        Some(value) => value,
        None => {
            assert!(solver.get_value(&one).is_some(), "expected ground FP value");
            return;
        }
    };

    assert!(matches!(
        value,
        ModelValue::Float(fp)
            if fp.sort == (FloatSort {
                exponent_bits: 8,
                significand_bits: 24
            })
    ));
}
