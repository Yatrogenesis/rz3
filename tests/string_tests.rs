use rz3::ast::{Expr, Type};
use rz3::Rz3Solver;
use rz3::SolverResult;

#[test]
fn test_string_length() {
    let mut solver = Rz3Solver::new();
    // (str.len "hello") = 5
    let hello = Expr::StrConst("hello".to_string());
    let len_hello = Expr::StrLen(Box::new(hello));

    // Assert: len("hello") != 5 -> Unsat
    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(len_hello),
        Box::new(Expr::Int(5)),
    ))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_string_var_len() {
    let mut solver = Rz3Solver::new();
    // s is a string, len(s) = 10, len(s) < 0 -> Unsat
    let s = Expr::Var("s".to_string(), Type::String);
    let len_s = Expr::StrLen(Box::new(s));

    solver.assert(&Expr::Eq(Box::new(len_s.clone()), Box::new(Expr::Int(10))));
    solver.assert(&Expr::Lt(Box::new(len_s), Box::new(Expr::Int(0))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}
