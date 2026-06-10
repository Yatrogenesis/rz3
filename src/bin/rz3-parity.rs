use rz3::parser::{Command as SmtCommand, Parser};
use rz3::{Rz3Solver, SolverResult};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, ExitCode};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CheckResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CaseReport {
    path: PathBuf,
    rz3: Vec<CheckResult>,
    z3: Option<Vec<CheckResult>>,
    status: CaseStatus,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CaseStatus {
    Match,
    Mismatch,
    ReferenceUnavailable,
    Rz3Error(String),
    Z3Error(String),
}

fn main() -> ExitCode {
    let args: Vec<OsString> = env::args_os().skip(1).collect();
    let root = args
        .first()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("benchmarks/smt2"));
    let z3_bin = env::var_os("Z3_BIN").unwrap_or_else(|| OsString::from("z3"));

    let files = match collect_smt2_files(&root) {
        Ok(files) => files,
        Err(err) => {
            eprintln!("failed to read benchmark path {}: {}", root.display(), err);
            return ExitCode::from(2);
        }
    };
    if files.is_empty() {
        eprintln!("no .smt2 files found under {}", root.display());
        return ExitCode::from(2);
    }

    let mut saw_mismatch = false;
    let mut saw_reference_unavailable = false;
    println!("file\trz3\tz3\tstatus");
    for path in files {
        let report = run_case(&path, &z3_bin);
        match &report.status {
            CaseStatus::Mismatch | CaseStatus::Rz3Error(_) | CaseStatus::Z3Error(_) => {
                saw_mismatch = true;
            }
            CaseStatus::ReferenceUnavailable => saw_reference_unavailable = true,
            CaseStatus::Match => {}
        }
        println!(
            "{}\t{}\t{}\t{}",
            report.path.display(),
            format_results(&report.rz3),
            report
                .z3
                .as_ref()
                .map(|results| format_results(results))
                .unwrap_or_else(|| "n/a".to_string()),
            format_status(&report.status)
        );
    }

    if saw_mismatch {
        ExitCode::from(1)
    } else if saw_reference_unavailable {
        ExitCode::from(2)
    } else {
        ExitCode::SUCCESS
    }
}

fn collect_smt2_files(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    collect_smt2_files_inner(root, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect_smt2_files_inner(path: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    if path.is_file() {
        if path.extension().is_some_and(|ext| ext == "smt2") {
            out.push(path.to_path_buf());
        }
        return Ok(());
    }
    if path.is_dir() {
        let mut entries = Vec::new();
        for entry in fs::read_dir(path)? {
            entries.push(entry?.path());
        }
        entries.sort();
        for entry in entries {
            collect_smt2_files_inner(&entry, out)?;
        }
    }
    Ok(())
}

fn run_case(path: &Path, z3_bin: &OsString) -> CaseReport {
    let input = match fs::read_to_string(path) {
        Ok(input) => input,
        Err(err) => {
            return CaseReport {
                path: path.to_path_buf(),
                rz3: Vec::new(),
                z3: None,
                status: CaseStatus::Rz3Error(err.to_string()),
            };
        }
    };
    let rz3 = run_rz3_input(&input);
    let z3 = run_z3(path, z3_bin);
    let status = match (&rz3, &z3) {
        (Err(err), _) => CaseStatus::Rz3Error(err.clone()),
        (_, Err(Z3RunError::Unavailable)) => CaseStatus::ReferenceUnavailable,
        (_, Err(Z3RunError::Failed(err))) => CaseStatus::Z3Error(err.clone()),
        (Ok(rz3_results), Ok(z3_results)) if rz3_results == z3_results => CaseStatus::Match,
        (Ok(_), Ok(_)) => CaseStatus::Mismatch,
    };
    CaseReport {
        path: path.to_path_buf(),
        rz3: rz3.unwrap_or_default(),
        z3: z3.ok(),
        status,
    }
}

fn run_rz3_input(input: &str) -> Result<Vec<CheckResult>, String> {
    let mut parser = Parser::new(input);
    let mut solver = Rz3Solver::new();
    let mut results = Vec::new();
    while let Some(command) = parser.parse_command() {
        match command {
            SmtCommand::SetLogic(_) | SmtCommand::SetOption(_, _) | SmtCommand::SetInfo(_, _) => {}
            SmtCommand::DeclareFun(name, params, return_type) => {
                solver.declare_fun_signature(name, params, return_type);
            }
            SmtCommand::DefineFun(name, params, return_type, _) => {
                let param_types = params.into_iter().map(|(_, ty)| ty).collect();
                solver.declare_fun_signature(name, param_types, return_type);
            }
            SmtCommand::Assert(expr) => solver.assert(&expr),
            SmtCommand::Push(n) => {
                for _ in 0..n {
                    solver.push();
                }
            }
            SmtCommand::Pop(n) => {
                for _ in 0..n {
                    solver.pop();
                }
            }
            SmtCommand::CheckSat => results.push(convert_result(solver.check())),
            SmtCommand::GetModel | SmtCommand::GetValue(_) => {}
            SmtCommand::Exit => break,
        }
    }
    if results.is_empty() {
        results.push(convert_result(solver.check()));
    }
    Ok(results)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Z3RunError {
    Unavailable,
    Failed(String),
}

fn run_z3(path: &Path, z3_bin: &OsString) -> Result<Vec<CheckResult>, Z3RunError> {
    let output = match ProcessCommand::new(z3_bin).arg("-smt2").arg(path).output() {
        Ok(output) => output,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Err(Z3RunError::Unavailable),
        Err(err) => return Err(Z3RunError::Failed(err.to_string())),
    };
    if !output.status.success() {
        return Err(Z3RunError::Failed(
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    parse_z3_stdout(&String::from_utf8_lossy(&output.stdout))
        .ok_or_else(|| Z3RunError::Failed("z3 produced no check-sat result".to_string()))
}

fn parse_z3_stdout(stdout: &str) -> Option<Vec<CheckResult>> {
    let results: Vec<CheckResult> = stdout.lines().filter_map(parse_result_line).collect();
    if results.is_empty() {
        None
    } else {
        Some(results)
    }
}

fn parse_result_line(line: &str) -> Option<CheckResult> {
    match line.trim() {
        "sat" => Some(CheckResult::Sat),
        "unsat" => Some(CheckResult::Unsat),
        "unknown" => Some(CheckResult::Unknown),
        _ => None,
    }
}

fn convert_result(result: SolverResult) -> CheckResult {
    match result {
        SolverResult::Sat => CheckResult::Sat,
        SolverResult::Unsat => CheckResult::Unsat,
        SolverResult::Unknown => CheckResult::Unknown,
    }
}

fn format_results(results: &[CheckResult]) -> String {
    results
        .iter()
        .map(|result| match result {
            CheckResult::Sat => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown => "unknown",
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn format_status(status: &CaseStatus) -> String {
    match status {
        CaseStatus::Match => "match".to_string(),
        CaseStatus::Mismatch => "mismatch".to_string(),
        CaseStatus::ReferenceUnavailable => "reference-unavailable".to_string(),
        CaseStatus::Rz3Error(err) => format!("rz3-error:{}", err),
        CaseStatus::Z3Error(err) => format!("z3-error:{}", err),
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_z3_stdout, run_rz3_input, CheckResult};

    #[test]
    fn parses_multiple_z3_results_deterministically() {
        let stdout = "sat\nunsupported\nunsat\nunknown\n";
        let results = match parse_z3_stdout(stdout) {
            Some(results) => results,
            None => panic!("expected parsed z3 results"),
        };
        assert_eq!(
            results,
            vec![CheckResult::Sat, CheckResult::Unsat, CheckResult::Unknown]
        );
    }

    #[test]
    fn runs_rz3_lra_case_in_process() {
        let input = "(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (> x 0))\n(check-sat)\n";
        let results = run_rz3_input(input);
        assert!(matches!(results, Ok(ref r) if r == &vec![CheckResult::Sat]));
    }
}
