use rz3::parser::{Command, Parser};
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

    let mut printed_check_sat = false;
    while let Some(command) = parser.parse_command() {
        match command {
            Command::SetLogic(_) | Command::SetOption(_, _) | Command::SetInfo(_, _) => {}
            Command::DeclareFun(name, params, return_type) => {
                solver.declare_fun_signature(name, params, return_type);
            }
            Command::DefineFun(name, params, return_type, _) => {
                let param_types = params.into_iter().map(|(_, ty)| ty).collect();
                solver.declare_fun_signature(name, param_types, return_type);
            }
            Command::Assert(expr) => solver.assert(&expr),
            Command::Push(n) => {
                for _ in 0..n {
                    solver.push();
                }
            }
            Command::Pop(n) => {
                for _ in 0..n {
                    solver.pop();
                }
            }
            Command::CheckSat => {
                print_result(solver.check());
                printed_check_sat = true;
            }
            Command::GetModel | Command::Exit => {}
        }
    }

    if !printed_check_sat {
        print_result(solver.check());
    }
}

fn print_result(result: SolverResult) {
    match result {
        SolverResult::Sat => println!("sat"),
        SolverResult::Unsat => println!("unsat"),
        SolverResult::Unknown => println!("unknown"),
    }
}
