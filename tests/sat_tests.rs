use rz3::sat::CdclSolver;

#[test]
fn test_basic_sat() {
    let mut solver = CdclSolver::new();
    // (x1 or x2) and (not x1 or x2)
    solver.add_clause(vec![1, 2]);
    solver.add_clause(vec![-1, 2]);
    assert!(solver.solve());
}

#[test]
fn test_basic_unsat() {
    let mut solver = CdclSolver::new();
    // (x1) and (not x1)
    solver.add_clause(vec![1]);
    solver.add_clause(vec![-1]);
    assert!(!solver.solve());
}

#[test]
fn test_3sat_unsat() {
    let mut solver = CdclSolver::new();
    // (x1 or x2 or x3) and (x1 or x2 or not x3) and (x1 or not x2 or x3) and (x1 or not x2 or not x3)
    // and (not x1 or x2 or x3) and (not x1 or x2 or not x3) and (not x1 or not x2 or x3) and (not x1 or not x2 or not x3)
    solver.add_clause(vec![1, 2, 3]);
    solver.add_clause(vec![1, 2, -3]);
    solver.add_clause(vec![1, -2, 3]);
    solver.add_clause(vec![1, -2, -3]);
    solver.add_clause(vec![-1, 2, 3]);
    solver.add_clause(vec![-1, 2, -3]);
    solver.add_clause(vec![-1, -2, 3]);
    solver.add_clause(vec![-1, -2, -3]);
    assert!(!solver.solve());
}
