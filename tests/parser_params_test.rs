
use rz3::parser::Parser;

#[test]
fn test_parse_declare_fun_params() {
    let input = "(declare-fun f ((x Real) (y Real)) Real)";
    let mut parser = Parser::new(input);
    let _cmd = parser.parse_command().unwrap();
    // This should work with the current implementation if it parses 
    // but we need to check if it properly handles the parameters.
    // Currently, it only handles empty params () and ignores them.
    // I should assert what it should do, but for now, let's see if it parses.
}
