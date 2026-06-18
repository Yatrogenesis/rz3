use rz3::ast::{Expr, Type};
use rz3::Rz3Solver;
use rz3::SolverResult;

#[test]
fn test_array_basic_select_store() {
    let mut solver = Rz3Solver::new();
    // a[i <- v][i] = v
    let a = Expr::Var(
        "a".to_string(),
        Type::Array(Box::new(Type::Int), Box::new(Type::Int)),
    );
    let i = Expr::Var("i".to_string(), Type::Int);
    let v = Expr::Var("v".to_string(), Type::Int);

    let store_a = Expr::Store(Box::new(a), Box::new(i.clone()), Box::new(v.clone()));
    let select_store = Expr::Select(Box::new(store_a), Box::new(i.clone()));

    // Assert: select(store(a, i, v), i) != v -> Unsat
    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(select_store),
        Box::new(v),
    ))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_array_diff_indices() {
    let mut solver = Rz3Solver::new();
    // i != j => a[i <- v][j] = a[j]
    let a = Expr::Var(
        "a".to_string(),
        Type::Array(Box::new(Type::Int), Box::new(Type::Int)),
    );
    let i = Expr::Var("i".to_string(), Type::Int);
    let j = Expr::Var("j".to_string(), Type::Int);
    let v = Expr::Var("v".to_string(), Type::Int);

    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(i.clone()),
        Box::new(j.clone()),
    ))));

    let store_a = Expr::Store(Box::new(a.clone()), Box::new(i), Box::new(v));
    let select_store = Expr::Select(Box::new(store_a), Box::new(j.clone()));
    let select_a = Expr::Select(Box::new(a), Box::new(j));

    // Assert: i != j AND select(store(a, i, v), j) != select(a, j) -> Unsat
    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(select_store),
        Box::new(select_a),
    ))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}
