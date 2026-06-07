use rz3::parser::Parser;
use rz3::Rz3Solver;
use rz3::SolverResult;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: rz3 <file.smt2>");
        return;
    }

    let input = fs::read_to_string(&args[1]).expect("Failed to read file");
    let mut parser = Parser::new(&input);
    let mut solver = Rz3Solver::new();

    while let Some(expr) = parser.parse_expr() {
        solver.assert(&expr);
    }

    match solver.check() {
        SolverResult::Sat => println!("sat"),
        SolverResult::Unsat => println!("unsat"),
        SolverResult::Unknown => println!("unknown"),
    }
}
