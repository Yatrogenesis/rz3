use rz3::ast::Expr;
use rz3::parser::Command;
use rz3::parser::Parser;

#[test]
fn test_parse_nested() {
    let mut parser = Parser::new("(<= (+ x (* y 2)) 10)");
    let expr = parser.parse_expr().unwrap();
    assert!(matches!(expr, Expr::Le(_, _)));
    let Expr::Le(lhs, rhs) = expr else {
        return;
    };
    assert!(matches!(*lhs, Expr::Add(_)));
    assert!(matches!(*rhs, Expr::Int(10)));
}

#[test]
fn test_parse_basic() {
    let mut parser = Parser::new("(<= (+ x y) 10)");
    let expr = parser.parse_expr().unwrap();
    assert!(matches!(expr, Expr::Le(_, _)));
    let Expr::Le(lhs, rhs) = expr else {
        return;
    };
    assert!(matches!(*lhs, Expr::Add(_)));
    let Expr::Add(args) = *lhs else {
        return;
    };
    assert_eq!(args.len(), 2);
    assert!(matches!(*rhs, Expr::Int(10)));
}

#[test]
fn test_parse_set_info() {
    let mut parser = Parser::new("(set-info :smt-lib-version 2.6)");
    let cmd = parser.parse_command().unwrap();
    assert!(matches!(cmd, Command::SetInfo(_, _)));
    let Command::SetInfo(key, value) = cmd else {
        return;
    };
    assert_eq!(key, ":smt-lib-version");
    assert_eq!(value, "2.6");
}
