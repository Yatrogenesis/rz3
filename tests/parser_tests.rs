use rz3::parser::Parser;
use rz3::ast::Expr;
use rz3::parser::Command;

#[test]
fn test_parse_nested() {
    let mut parser = Parser::new("(<= (+ x (* y 2)) 10)");
    let expr = parser.parse_expr().unwrap();
    if let Expr::Le(lhs, rhs) = expr {
        // Assert structure: (+ x (* y 2))
        assert!(matches!(*lhs, Expr::Add(_)));
        assert!(matches!(*rhs, Expr::Int(10)));
    } else {
        panic!("Should be Le");
    }
}

#[test]
fn test_parse_basic() {
    let mut parser = Parser::new("(<= (+ x y) 10)");
    let expr = parser.parse_expr().unwrap();
    if let Expr::Le(lhs, rhs) = expr {
        if let Expr::Add(args) = *lhs {
            assert_eq!(args.len(), 2);
        } else {
            panic!("LHS should be Add");
        }
        assert!(matches!(*rhs, Expr::Int(10)));
    } else {
        panic!("Should be Le");
    }
}

#[test]
fn test_parse_set_info() {
    let mut parser = Parser::new("(set-info :smt-lib-version 2.6)");
    let cmd = parser.parse_command().unwrap();
    if let Command::SetInfo(key, value) = cmd {
        assert_eq!(key, ":smt-lib-version");
        assert_eq!(value, "2.6");
    } else {
        panic!("Should be SetInfo");
    }
}

