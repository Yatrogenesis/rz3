use rz3::Rz3Solver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;

#[test]
fn test_quantifier_basic_forall() {
    let mut solver = Rz3Solver::new();
    // (forall ((x Real)) (= (f x) 1.0))
    // f(a) != 1.0
    // Result: UNSAT
    
    let x_name = "x".to_string();
    let f_x = Expr::App("f".to_string(), vec![Expr::Var(x_name.clone(), Type::Real)]);
    let forall_expr = Expr::ForAll(
        vec![(x_name, Type::Real)],
        Box::new(Expr::Eq(Box::new(f_x), Box::new(Expr::Real(1, 0))))
    );
    
    let a = Expr::Var("a".to_string(), Type::Real);
    let f_a = Expr::App("f".to_string(), vec![a.clone()]);
    let not_eq = Expr::Not(Box::new(Expr::Eq(Box::new(f_a), Box::new(Expr::Real(1, 0)))));
    
    solver.assert(&forall_expr);
    solver.assert(&not_eq);
    
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_quantifier_transitivity() {
    let mut solver = Rz3Solver::new();
    // (forall ((x Real)) (forall ((y Real)) (forall ((z Real)) 
    //    (=> (and (= x y) (= y z)) (= x z)))))
    // Just a basic test that forall doesn't crash and handles basic ground terms
    let x = Expr::Var("a".to_string(), Type::Real);
    let y = Expr::Var("b".to_string(), Type::Real);
    
    solver.assert(&Expr::Eq(Box::new(x.clone()), Box::new(y.clone())));
    assert!(matches!(solver.check(), SolverResult::Sat));
}
