use rz3::theory::NlaSolver;
use rz3::ast::{Expr, Type};
use rz3::SolverResult;
use rz3::Rz3Solver;
use num_bigint::BigInt;

#[test]
fn test_expr_to_poly_conversion() {
    let mut solver = NlaSolver::new();
    let e1 = Expr::Add(vec![Expr::Int(5), Expr::Int(3)]);
    let poly = solver.expr_to_poly(&e1).unwrap();
    // 5 + 3 = 8
    assert_eq!(poly.terms.get(&vec![]).unwrap(), &BigInt::from(8));
}

#[test]
fn test_expr_to_poly_mul_conversion() {
    let mut solver = NlaSolver::new();
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    
    // x * y
    let e1 = Expr::Mul(vec![x, y]);
    let poly = solver.expr_to_poly(&e1).unwrap();
    
    // Expected: x^1 * y^1 => [1, 1]
    let term = vec![1, 1];
    assert_eq!(poly.terms.get(&term).unwrap(), &BigInt::from(1));
}

#[test]
fn test_expr_to_poly_determinism() {
    let mut solver = NlaSolver::new();
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    
    let e1 = Expr::Add(vec![
        Expr::Mul(vec![x.clone(), x.clone()]),
        Expr::Mul(vec![Expr::Int(2), x, y]),
    ]);
    
    let mut hashes = Vec::new();
    for _ in 0..30 {
        solver.reset();
        let poly = solver.expr_to_poly(&e1).unwrap();
        
        let mut entries: Vec<_> = poly.terms.iter().collect();
        entries.sort_by(|a, b| a.0.cmp(b.0));
        let s = format!("{:?}", entries);
        hashes.push(s);
    }
    
    let first = hashes[0].clone();
    for h in hashes {
        assert_eq!(h, first);
    }
}

#[test]
fn test_nla_basic_conflict() {
    let mut solver = Rz3Solver::new();
    // x * x + 1 < 0  -> UNSAT (High-Fidelity CAD-lite should catch this)
    let x = Expr::Var("x".to_string(), Type::Real);
    let x_sq = Expr::Mul(vec![x.clone(), x.clone()]);
    let x_sq_plus_1 = Expr::Add(vec![x_sq, Expr::Int(1)]);
    let zero = Expr::Int(0);
    let constraint = Expr::Lt(Box::new(x_sq_plus_1), Box::new(zero));
    
    solver.assert(&constraint);
    
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn test_nla_sat() {
    let mut solver = Rz3Solver::new();
    let x = Expr::Var("x".to_string(), Type::Real);
    let y = Expr::Var("y".to_string(), Type::Real);
    let xy = Expr::Mul(vec![x, y]);
    let zero = Expr::Int(0);
    let constraint = Expr::Gt(Box::new(xy), Box::new(zero));
    
    solver.assert(&constraint);
    
    // As basic NLA doesn't know how to solve xy > 0, it should return Sat (no conflict found)
    assert!(matches!(solver.check(), SolverResult::Sat));
}
