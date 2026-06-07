
use rz3::parser::Parser;
use rz3::parser::Command;
use rz3::ast::Expr;
use rz3::ast::Type;

#[test]
fn test_define_fun_basic() {
    let input = "(define-fun f () Int 1)";
    let mut parser = Parser::new(input);
    let cmd = parser.parse_command().unwrap();
    
    if let Command::DefineFun(name, params, ret_type, body) = cmd {
        assert_eq!(name, "f");
        assert_eq!(params.len(), 0);
        assert_eq!(ret_type, Type::Int);
        assert_eq!(body, Expr::Int(1));
    } else {
        panic!("Expected DefineFun");
    }
}

#[test]
fn test_define_fun_with_params() {
    let input = "(define-fun g ((x Int) (y Int)) Int (+ x y))";
    let mut parser = Parser::new(input);
    let cmd = parser.parse_command().unwrap();
    
    if let Command::DefineFun(name, params, ret_type, _body) = cmd {
        assert_eq!(name, "g");
        assert_eq!(params.len(), 2);
        assert_eq!(params[0].0, "x");
        assert_eq!(params[0].1, Type::Int);
        assert_eq!(params[1].0, "y");
        assert_eq!(params[1].1, Type::Int);
        assert_eq!(ret_type, Type::Int);
        // We don't need to check body intensely for now, 
        // as long as it parses correctly.
    } else {
        panic!("Expected DefineFun");
    }
}

#[test]
fn test_define_fun_complex() {
    let input = "(define-fun h ((x Real)) Real (ite (<= x 0.0) 0.0 x))";
    let mut parser = Parser::new(input);
    let cmd = parser.parse_command().unwrap();
    
    if let Command::DefineFun(name, params, ret_type, _body) = cmd {
        assert_eq!(name, "h");
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].0, "x");
        assert_eq!(params[0].1, Type::Real);
        assert_eq!(ret_type, Type::Real);
    } else {
        panic!("Expected DefineFun");
    }
}
