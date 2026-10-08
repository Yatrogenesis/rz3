//! Runs a whole SMT-LIB script through the strict front end and the solver.
//!
//! Shared by the regression tests and tools so the text path (lexer, parser,
//! `let`/`define-fun` expansion, solver) is exercised exactly as the CLI does.

use crate::parser::{Command, Parser};
use crate::{Rz3Solver, SolverResult};

/// One result per `(check-sat)`; a script with none gets a single implicit check, as the
/// CLI does. Any lexical, syntactic or unsupported-feature problem is an `Err`: a
/// verdict is never produced from a script that was only partly understood.
pub fn check_script(input: &str) -> Result<Vec<SolverResult>, String> {
    let mut parser = Parser::strict(input);
    let mut solver = Rz3Solver::new();
    let mut results = Vec::new();
    while let Some(command) = parser.parse_command() {
        match command {
            Command::DeclareFun(name, params, ret) => {
                solver.declare_fun_signature(name, params, ret);
            }
            Command::Assert(expr) => solver.assert(&expr),
            Command::Push(n) => (0..n).for_each(|_| solver.push()),
            Command::Pop(n) => (0..n).for_each(|_| solver.pop()),
            Command::CheckSat => results.push(solver.check()),
            Command::Exit => break,
            Command::SetLogic(_)
            | Command::SetOption(_, _)
            | Command::SetInfo(_, _)
            | Command::DefineFun(_, _, _, _)
            | Command::GetModel
            | Command::GetValue(_)
            | Command::Skipped(_) => {}
        }
    }
    if let Some(err) = parser.error() {
        return Err(err.to_string());
    }
    if results.is_empty() {
        results.push(solver.check());
    }
    Ok(results)
}
