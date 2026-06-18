use rz3::parser::Parser;

#[test]
fn test_parse_complex_smtlib() {
    let input = "(set-logic QF_LRA)
                 (set-option :produce-models true)
                 (declare-fun x () Real)
                 (declare-fun y () Real)
                 (assert (and (>= x 0.0) (<= (+ x y) 10.0)))
                 (check-sat)
                 (get-model)";

    // We expect the parser to handle this without erroring out on set-option
    // and successfully parsing the commands.
    let mut parser = Parser::new(input);

    // This is just a starting test.
    let mut commands = Vec::new();
    while let Some(cmd) = parser.parse_command() {
        commands.push(cmd);
    }

    assert!(commands.len() >= 6);
}
