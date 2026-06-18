use rz3::ast::Expr;
use rz3::tactic::Simplifier;

#[test]
fn test_simplify_boolean() {
    // A AND true -> A
    let a = Expr::Var("a".to_string(), rz3::ast::Type::Bool);
    let expr = Expr::And(vec![a.clone(), Expr::Bool(true)]);
    let simplified = Simplifier::simplify(expr);
    assert_eq!(simplified, a);
}

#[test]
fn test_simplify_double_negation() {
    // NOT NOT A -> A
    let a = Expr::Var("a".to_string(), rz3::ast::Type::Bool);
    let expr = Expr::Not(Box::new(Expr::Not(Box::new(a.clone()))));
    let simplified = Simplifier::simplify(expr);
    assert_eq!(simplified, a);
}

#[test]
fn test_simplify_arithmetic() {
    // x + 2 + 3 -> x + 5
    let x = Expr::Var("x".to_string(), rz3::ast::Type::Int);
    let expr = Expr::Add(vec![x.clone(), Expr::Int(2), Expr::Int(3)]);
    let simplified = Simplifier::simplify(expr);
    // Nota: El simplificador actual pone las constantes al final
    assert!(matches!(simplified, Expr::Add(_)));
    let Expr::Add(args) = simplified else {
        return;
    };
    assert!(args.contains(&x));
    assert!(args.contains(&Expr::Int(5)));
}

#[test]
fn test_simplify_ite() {
    // (ite true x y) -> x
    let x = Expr::Var("x".to_string(), rz3::ast::Type::Int);
    let y = Expr::Var("y".to_string(), rz3::ast::Type::Int);
    let expr = Expr::Ite(Box::new(Expr::Bool(true)), Box::new(x.clone()), Box::new(y));
    let simplified = Simplifier::simplify(expr);
    assert_eq!(simplified, x);
}
