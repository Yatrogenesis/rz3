use rz3::Rz3Solver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;

#[test]
fn test_lra_basic_sat() {
    let mut solver = Rz3Solver::new();
    // x + y <= 10, x >= 5, y >= 6 -> Unsat
    // x + y <= 10, x >= 2, y >= 3 -> Sat
    
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    
    solver.assert(&Expr::Le(
        Box::new(Expr::Add(vec![x.clone(), y.clone()])),
        Box::new(Expr::Int(10))
    ));
    solver.assert(&Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(2))));
    solver.assert(&Expr::Ge(Box::new(y.clone()), Box::new(Expr::Int(3))));
    
    assert!(matches!(solver.check(), SolverResult::Sat));
}

#[test]
fn test_lra_basic_unsat() {
    let mut solver = Rz3Solver::new();
    // x + y <= 10, x >= 6, y >= 5 -> Unsat
    
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    
    solver.assert(&Expr::Le(
        Box::new(Expr::Add(vec![x.clone(), y.clone()])),
        Box::new(Expr::Int(10))
    ));
    solver.assert(&Expr::Ge(Box::new(x.clone()), Box::new(Expr::Int(6))));
    solver.assert(&Expr::Ge(Box::new(y.clone()), Box::new(Expr::Int(5))));
    
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_euf_congruence() {
    let mut solver = Rz3Solver::new();
    // x = y => f(x) = f(y)
    // Assert: x = y, f(x) != f(y) -> Unsat
    
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    let fx = Expr::App("f".to_string(), vec![x.clone()]);
    let fy = Expr::App("f".to_string(), vec![y.clone()]);
    
    solver.assert(&Expr::Eq(Box::new(x), Box::new(y)));
    solver.assert(&Expr::Not(Box::new(Expr::Eq(Box::new(fx), Box::new(fy)))));
    
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_euf_transitivity() {
    let mut solver = Rz3Solver::new();
    // x = y, y = z, f(x) != f(z) -> Unsat
    
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    let z = Expr::Var("z".to_string(), Type::Real);
    let fx = Expr::App("f".to_string(), vec![x.clone()]);
    let fz = Expr::App("f".to_string(), vec![z.clone()]);
    
    solver.assert(&Expr::Eq(Box::new(x), Box::new(y.clone())));
    solver.assert(&Expr::Eq(Box::new(y), Box::new(z)));
    solver.assert(&Expr::Not(Box::new(Expr::Eq(Box::new(fx), Box::new(fz)))));
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_bv_basic_sat() {
    let mut solver = Rz3Solver::new();
    // x + 2 = 5 (8-bit)
    let x = Expr::Var("x".to_string(), Type::BitVec(8));
    let two = Expr::BvConst(2, 8);
    let five = Expr::BvConst(5, 8);
    
    solver.assert(&Expr::Eq(
        Box::new(Expr::BvAdd(Box::new(x), Box::new(two))),
        Box::new(five)
    ));
    
    assert!(matches!(solver.check(), SolverResult::Sat));
}

#[test]
fn test_bv_basic_unsat() {
    let mut solver = Rz3Solver::new();
    // x & 1 = 0, x & 1 = 1
    let x = Expr::Var("x".to_string(), Type::BitVec(8));
    let one = Expr::BvConst(1, 8);
    let zero = Expr::BvConst(0, 8);
    
    solver.assert(&Expr::Eq(
        Box::new(Expr::BvAnd(Box::new(x.clone()), Box::new(one.clone()))),
        Box::new(zero)
    ));
    solver.assert(&Expr::Eq(
        Box::new(Expr::BvAnd(Box::new(x), Box::new(one))),
        Box::new(Expr::BvConst(1, 8))
    ));
    
    let result = solver.check();
    if matches!(result, SolverResult::Sat) {
        let model = solver.get_model();
        println!("Model found: {:?}", model);
    }
    assert!(matches!(result, SolverResult::Unsat));
}


