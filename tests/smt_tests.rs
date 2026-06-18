use rz3::ast::{Expr, Type};
use rz3::Rz3Solver;
use rz3::SolverResult;

#[test]
fn test_smt_basic() {
    let mut solver = Rz3Solver::new();
    // (a or (x + y <= 10)) and (not a) and (x >= 6) and (y >= 5) -> Unsat

    let a = Expr::Var("a".to_string(), Type::Bool);
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);

    let x_plus_y_le_10 = Expr::Le(
        Box::new(Expr::Add(vec![x.clone(), y.clone()])),
        Box::new(Expr::Int(10)),
    );

    solver.assert(&Expr::Or(vec![a.clone(), x_plus_y_le_10]));
    solver.assert(&Expr::Not(Box::new(a.clone())));
    solver.assert(&Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(6))));
    solver.assert(&Expr::Ge(Box::new(y.clone()), Box::new(Expr::Int(5))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_smt_sat() {
    let mut solver = Rz3Solver::new();
    // (a or (x + y <= 10)) and (not a) and (x >= 2) and (y >= 3) -> Sat

    let a = Expr::Var("a".to_string(), Type::Bool);
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);

    let x_plus_y_le_10 = Expr::Le(
        Box::new(Expr::Add(vec![x.clone(), y.clone()])),
        Box::new(Expr::Int(10)),
    );

    solver.assert(&Expr::Or(vec![a.clone(), x_plus_y_le_10]));
    solver.assert(&Expr::Not(Box::new(a.clone())));
    solver.assert(&Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(2))));
    solver.assert(&Expr::Ge(Box::new(y.clone()), Box::new(Expr::Int(3))));

    assert!(matches!(solver.check(), SolverResult::Sat));
}
