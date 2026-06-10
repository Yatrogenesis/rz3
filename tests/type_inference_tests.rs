use rz3::ast::{Expr, Type};
use rz3::parser::{Command, Parser};
use rz3::{Rz3Solver, SolverResult};

#[test]
fn unknown_application_does_not_default_to_int() {
    let app = Expr::App("f".to_string(), vec![Expr::Int(1)]);
    assert_eq!(app.get_type(), Type::Unknown);
}

#[test]
fn declare_fun_with_params_records_function_type() {
    let mut parser = Parser::new("(declare-fun f ((x Real) (y Int)) Bool)");
    let Some(command) = parser.parse_command() else {
        panic!("expected declare-fun command");
    };
    match command {
        Command::DeclareFun(name, params, ret) => {
            assert_eq!(name, "f");
            assert_eq!(params, vec![Type::Real, Type::Int]);
            assert_eq!(ret, Type::Bool);
        }
        other => assert!(
            matches!(other, Command::DeclareFun(_, _, _)),
            "expected declare-fun"
        ),
    }
}

#[test]
fn declare_fun_with_standard_smtlib_param_sorts_records_function_type() {
    let mut parser = Parser::new("(declare-fun f (Real Int) Bool)");
    let Some(command) = parser.parse_command() else {
        panic!("expected declare-fun command");
    };
    match command {
        Command::DeclareFun(name, params, ret) => {
            assert_eq!(name, "f");
            assert_eq!(params, vec![Type::Real, Type::Int]);
            assert_eq!(ret, Type::Bool);
        }
        other => assert!(
            matches!(other, Command::DeclareFun(_, _, _)),
            "expected declare-fun"
        ),
    }
}

#[test]
fn declare_fun_bitvec_sort_does_not_consume_next_command() {
    let mut parser = Parser::new("(declare-fun x () (_ BitVec 8))");
    let Some(command) = parser.parse_command() else {
        panic!("expected declare-fun command");
    };
    match command {
        Command::DeclareFun(name, params, Type::BitVec(width)) => {
            assert_eq!(name, "x");
            assert!(params.is_empty());
            assert_eq!(width, 8);
        }
        other => assert!(
            matches!(other, Command::DeclareFun(_, _, Type::BitVec(_))),
            "expected bit-vector declaration"
        ),
    }
}

#[test]
fn declared_bitvec_symbol_is_used_for_parsed_assertions() {
    let mut parser = Parser::new("(= x #b00000001)");
    let Some(expr) = parser.parse_expr() else {
        panic!("expected parsed bit-vector equality");
    };

    let mut solver = Rz3Solver::new();
    solver.declare_fun_signature("x".to_string(), Vec::new(), Type::BitVec(8));
    solver.assert(&expr);
    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(Expr::Var("x".to_string(), Type::BitVec(8))),
        Box::new(Expr::BvConst(1, 8)),
    ))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}
