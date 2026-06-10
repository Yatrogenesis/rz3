use rz3::ast::{Expr, Type};
use rz3::{Rz3Solver, SolverResult};

#[test]
fn boolean_function_congruence_uses_asserted_boolean_values() {
    let mut solver = Rz3Solver::new();
    solver.declare_fun_signature("p".to_string(), Vec::new(), Type::Bool);
    solver.declare_fun_signature("f".to_string(), vec![Type::Bool], Type::Bool);

    let p = Expr::Var("p".to_string(), Type::Bool);
    let fp = Expr::App("f".to_string(), vec![p.clone()]);
    let f_true = Expr::App("f".to_string(), vec![Expr::Bool(true)]);

    solver.assert(&p);
    solver.assert(&Expr::Not(Box::new(Expr::Eq(
        Box::new(fp),
        Box::new(f_true),
    ))));

    assert!(matches!(solver.check(), SolverResult::Unsat));
}
