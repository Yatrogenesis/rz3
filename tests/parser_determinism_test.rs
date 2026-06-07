
use rz3::parser::Parser;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

#[test]
fn test_parser_determinism() {
    let input = "(define-fun h ((x Real)) Real (ite (<= x 0.0) 0.0 x))";
    let mut outputs = Vec::new();
    
    for _ in 0..30 {
        let mut parser = Parser::new(input);
        let cmd = parser.parse_command().unwrap();
        // Since Command doesn't implement Hash, we hash its Debug representation
        let output_str = format!("{:?}", cmd);
        let mut hasher = DefaultHasher::new();
        output_str.hash(&mut hasher);
        outputs.push(hasher.finish());
    }
    
    // Check all are identical
    let first = outputs[0];
    for &o in &outputs[1..] {
        assert_eq!(first, o, "Parser output is not deterministic");
    }
}
