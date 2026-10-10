// End-to-end tests of the `rz3` command line: the real binary on small SMT-LIB scripts
// (tests/data/cli/*.smt2), checking exact stdout, stderr and exit status.
//
// The scripts double as Z3 inputs: every verdict and every model value pinned here was
// contrasted with `z3 -smt2` on the same file. Only the textual layout differs (Z3 breaks
// `define-fun` bodies onto their own line, prints bit-vectors as `#x..` where rz3 always
// prints `#b..`, and orders model entries differently); the values are identical.
// Behaviours where rz3 deliberately or accidentally differs from Z3 are called out in the
// comments, and the ones that look like defects are `#[ignore]` tests that assert the
// Z3-conformant behaviour.

use std::path::PathBuf;
use std::process::Command;

struct Out {
    stdout: String,
    stderr: String,
    code: Option<i32>,
}

fn data(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/cli")
        .join(format!("{name}.smt2"))
}

fn run_path(arg: Option<&std::ffi::OsStr>, envs: &[(&str, &str)]) -> Out {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_rz3"));
    cmd.env_remove("RZ3_STATS").env_remove("RZ3_DEADLINE_MS");
    if let Some(a) = arg {
        cmd.arg(a);
    }
    for (k, v) in envs {
        cmd.env(k, v);
    }
    let o = cmd.output().expect("failed to run the rz3 binary");
    Out {
        stdout: String::from_utf8(o.stdout).expect("stdout is UTF-8"),
        stderr: String::from_utf8(o.stderr).expect("stderr is UTF-8"),
        code: o.status.code(),
    }
}

fn run(name: &str) -> Out {
    run_path(Some(data(name).as_os_str()), &[])
}

fn run_env(name: &str, envs: &[(&str, &str)]) -> Out {
    run_path(Some(data(name).as_os_str()), envs)
}

/// Asserts exact stdout, empty stderr and the given exit code.
fn expect(name: &str, stdout: &str, code: i32) {
    let o = run(name);
    assert_eq!(o.stdout, stdout, "stdout of {name}");
    assert_eq!(o.stderr, "", "stderr of {name}");
    assert_eq!(o.code, Some(code), "exit status of {name}");
}

// ------------------------------------------------------------------ verdicts

#[test]
fn sat_verdict() {
    expect("sat_int", "sat\n", 0);
}

#[test]
fn unsat_verdict() {
    expect("unsat_int", "unsat\n", 0);
}

// Z3 answers `sat` for both (an irrational root, an unbounded quantifier alternation);
// rz3 is incomplete there and must say `unknown`, never a wrong sat/unsat. get-model and
// get-value after `unknown` print nothing.
#[test]
fn unknown_verdict_nonlinear_real() {
    expect("unknown_nonlinear", "unknown\n", 0);
}

#[test]
fn unknown_verdict_quantifier() {
    expect("unknown_quantifier", "unknown\n", 0);
}

#[test]
fn verdict_is_deterministic_across_runs() {
    let first = run("model_real").stdout;
    for _ in 0..5 {
        assert_eq!(run("model_real").stdout, first);
    }
}

// ------------------------------------------------------------------ get-model

#[test]
fn get_model_integers() {
    expect(
        "model_int",
        "sat\n(\n  (define-fun big () Int 123456789012345678901234567890)\n  (define-fun x () Int (- 4))\n  (define-fun y () Int 7)\n  (define-fun z () Int 0)\n)\n",
        0,
    );
}

#[test]
fn get_model_reals() {
    expect(
        "model_real",
        "sat\n(\n  (define-fun a () Real (- (/ 1.0 2.0)))\n  (define-fun b () Real 3.0)\n  (define-fun c () Real 0.0)\n  (define-fun d () Real (/ 2.0 3.0))\n  (define-fun e () Real (- 3.0))\n  (define-fun f () Real (- (/ 7.0 3.0)))\n)\n",
        0,
    );
}

#[test]
fn get_model_booleans_and_bitvectors() {
    expect(
        "model_bool_bv",
        concat!(
            "sat\n(\n",
            "  (define-fun b8 () (_ BitVec 8) #b00101010)\n",
            "  (define-fun c4 () (_ BitVec 4) #b0101)\n",
            "  (define-fun one () (_ BitVec 1) #b1)\n",
            "  (define-fun p () Bool true)\n",
            "  (define-fun q () Bool false)\n",
            "  (define-fun wide () (_ BitVec 100) #b",
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
            ")\n",
            "  (define-fun zero () (_ BitVec 4) #b0000)\n",
            ")\n"
        ),
        0,
    );
}

// Z3 refuses get-model before a check-sat ("model is not available"); rz3 runs the check
// itself, prints its verdict first and then answers.
#[test]
fn get_model_before_any_check_sat_checks_first() {
    expect(
        "get_model_without_check",
        "sat\n(\n  (define-fun x () Int 5)\n)\nsat\n",
        0,
    );
}

#[test]
fn get_value_before_any_check_sat_checks_first() {
    expect("get_value_without_check", "sat\n((x 5))\n", 0);
}

// Z3 prints `(error "model is not available")` here; rz3 stays silent after `unsat`.
#[test]
fn get_model_and_get_value_after_unsat_print_nothing() {
    expect("get_model_after_unsat", "unsat\n", 0);
}

// ------------------------------------------------------------------ get-value

#[test]
fn get_value_prints_term_and_exact_value() {
    expect(
        "get_value",
        concat!(
            "sat\n",
            "(((= x 7) true) ((not p) false) ((and p q) false) ((or p q) true) ((+ x 1 2) 10) ",
            "((- x 3) 4) ((- 10 x 1) 2) ((* x 2 3) 42) ((/ r 2.0) (/ 3.0 8.0)) ((< x 8) true) ",
            "((<= x 7) true) ((> x 7) false) ((>= x 8) false) ((ite p x 0) 7) ((ite q 1.5 r) (/ 3.0 4.0)))\n",
            "(((bvadd b c) #b10100101) ((bvsub b c) #b10000111) ((bvmul b c) #b11001010) ",
            "((bvand b c) #b00000110) ((bvor b c) #b10011111) ((bvxor b c) #b10011001) ",
            "((bvnot b) #b01101001) (((_ extract 7 4) b) #b1001))\n",
            "((x 7) (5 5) (2.5 (/ 5.0 2.0)) (true true) (#b00001111 #b00001111))\n"
        ),
        0,
    );
}

// DEFECT (reported, not fixed): the echoed term of operators missing from `format_expr`
// goes through the Rust Debug-style `Display`, e.g. `BvShl(Var("b", BitVec(8)), ...)`,
// which is not SMT-LIB. Z3 echoes the original term.
#[test]
#[ignore = "defect: get-value echo of bvshl/concat/bvneg/bvult/mod/div/to_int/is_int is not SMT-LIB"]
fn get_value_echoes_every_operator_as_smtlib() {
    let o = run("get_value_unsupported_echo");
    assert_eq!(
        o.stdout,
        "sat\n(((bvshl b c) #b00000000) ((concat b c) #b1001011000001111) ((bvneg b) #b01101010) ((bvult b c) false) ((mod x 4) 3) ((div x 2) 3) ((to_int r) 0) ((is_int r) false))\n"
    );
}

// Pins what is printed today for the same script (values are right, the echo is not).
#[test]
fn get_value_values_for_unsupported_echo_are_right_even_if_the_echo_is_not() {
    let o = run("get_value_unsupported_echo");
    assert_eq!(o.code, Some(0));
    assert!(o.stdout.starts_with("sat\n("), "{}", o.stdout);
    for value in [
        " #b00000000)",
        " #b1001011000001111)",
        " #b01101010)",
        " false)",
        " 3)",
        " 0)",
    ] {
        assert!(
            o.stdout.contains(value),
            "missing {value:?} in {}",
            o.stdout
        );
    }
}

// DEFECT (reported, not fixed): get-value silently drops applications of declared
// functions. Z3 answers `(((f x) 11) ((f 7) 11))`.
#[test]
#[ignore = "defect: get-value omits uninterpreted-function applications"]
fn get_value_of_uninterpreted_function_application() {
    expect("get_value_uf", "sat\n(((f x) 11) ((f 7) 11))\n", 0);
}

#[test]
fn get_value_uf_currently_prints_an_empty_list() {
    expect("get_value_uf", "sat\n()\n", 0);
}

// ------------------------------------------------------------------ errors

// A syntax or semantic error stops the run (fail closed): what was already decided is
// printed, then `(error "...")` on stdout and exit status 1. No verdict follows an error.
// Z3 instead keeps going after an error; the message texts differ.
#[test]
fn error_after_a_verdict_keeps_the_verdict_and_exits_1() {
    expect(
        "syntax_error_after_check",
        "sat\n(error \"unsupported or undeclared operator 'foo'\")\n",
        1,
    );
}

#[test]
fn error_in_truncated_input_prints_no_verdict() {
    expect(
        "syntax_error_truncated",
        "(error \"unexpected end of input\")\n",
        1,
    );
}

#[test]
fn error_undeclared_symbol_prints_no_verdict() {
    expect(
        "syntax_error_undeclared",
        "(error \"undeclared symbol 'y'\")\n",
        1,
    );
}

#[test]
fn error_unsupported_command_prints_no_verdict() {
    expect(
        "syntax_error_command",
        "(error \"unsupported command 'frobnicate'\")\n",
        1,
    );
}

// ------------------------------------------------------------------ session control

#[test]
fn several_check_sats_with_push_and_pop() {
    expect("push_pop", "sat\nunsat\nsat\nsat\n((x 10))\nsat\n", 0);
}

// Without any check-sat rz3 still answers once at the end (Z3 prints nothing).
#[test]
fn script_without_check_sat_prints_one_verdict_at_the_end() {
    expect("no_check_sat", "sat\n", 0);
    expect("no_check_sat_unsat", "unsat\n", 0);
}

#[test]
fn empty_script_prints_sat() {
    expect("empty", "sat\n", 0);
}

#[test]
fn exit_stops_processing() {
    expect("exit_stops", "sat\n", 0);
}

#[test]
fn set_option_set_info_set_logic_are_accepted_silently() {
    expect(
        "options_ignored",
        "sat\n(\n  (define-fun x () Int 2)\n)\nsat\n",
        0,
    );
}

// ------------------------------------------------------------------ process level

#[test]
fn no_arguments_prints_usage() {
    let o = run_path(None, &[]);
    assert_eq!(o.stdout, "Usage: rz3 <file.smt2>\n");
    assert_eq!(o.stderr, "");
    assert_eq!(o.code, Some(0));
}

#[test]
fn one_argument_is_enough() {
    // exactly one argument (the boundary of the usage check) runs the file
    let o = run("sat_int");
    assert_eq!(o.stdout, "sat\n");
}

#[test]
fn missing_file_reports_on_stderr_and_prints_no_verdict() {
    let missing = std::env::temp_dir().join("rz3_cli_no_such_file_7f3a.smt2");
    let o = run_path(Some(missing.as_os_str()), &[]);
    assert_eq!(o.stdout, "");
    assert!(
        o.stderr
            .starts_with(&format!("failed to read {}: ", missing.display())),
        "{}",
        o.stderr
    );
    assert!(o.stderr.ends_with('\n'));
}

// DEFECT (reported, not fixed): an unreadable input exits with status 0, so a caller that
// only checks the exit code cannot tell it from a successful run. Z3 exits non-zero.
#[test]
#[ignore = "defect: missing input file exits with status 0"]
fn missing_file_exits_nonzero() {
    let missing = std::env::temp_dir().join("rz3_cli_no_such_file_7f3a.smt2");
    let o = run_path(Some(missing.as_os_str()), &[]);
    assert_ne!(o.code, Some(0));
}

// The solver runs on a thread with a 2 GiB stack so that deeply nested terms (common in
// real benchmarks) do not overflow; on the default 8 MiB main stack this input would crash.
#[test]
fn deeply_nested_term_does_not_overflow_the_stack() {
    let depth = 60_000;
    let mut s = String::from("(declare-const p Bool)\n(assert ");
    for _ in 0..depth {
        s.push_str("(not ");
    }
    s.push('p');
    for _ in 0..depth {
        s.push(')');
    }
    s.push_str(")\n(check-sat)\n");
    let path = std::env::temp_dir().join(format!("rz3_cli_deep_{}.smt2", std::process::id()));
    std::fs::write(&path, s).unwrap();
    let o = run_path(Some(path.as_os_str()), &[]);
    let _ = std::fs::remove_file(&path);
    assert_eq!(o.stdout, "sat\n");
    assert_eq!(o.code, Some(0));
}

// ------------------------------------------------------------------ environment

#[test]
fn rz3_stats_writes_phase_breakdown_to_stderr_only() {
    let plain = run("sat_int");
    assert_eq!(plain.stderr, "");
    let o = run_env("sat_int", &[("RZ3_STATS", "1")]);
    assert_eq!(o.stdout, plain.stdout, "stats must never reach stdout");
    assert_eq!(o.code, Some(0));
    let lines: Vec<&str> = o.stderr.lines().collect();
    assert_eq!(lines.len(), 3, "{}", o.stderr);
    assert!(lines[0].starts_with("stats: assert_ms="));
    for key in [
        " sat_ms=",
        " theory_ms=",
        " certify_ms=",
        " check_calls=1 ",
        " dpll_iterations=",
        " theory_conflicts=",
        " branches=",
        " pivots=",
        " atoms=",
        " sat_vars=",
    ] {
        assert!(lines[0].contains(key), "missing {key:?} in {}", lines[0]);
    }
    assert!(lines[1].starts_with("stats: array_instances="));
    for key in [
        " sat_propagations=",
        " sat_decisions=",
        " sat_conflicts=",
        " sat_restarts=",
        " learned=",
    ] {
        assert!(lines[1].contains(key), "missing {key:?} in {}", lines[1]);
    }
    assert!(lines[2].starts_with("stats: lin_ms="));
    assert!(lines[2].contains(" dl_ms="));
    assert!(lines[2].contains("(repair "));
    assert!(lines[2].contains(", search "));
    assert!(lines[2].contains(") dl_propagations="));
    // timings are milliseconds with one decimal: a tiny script takes well under a second
    // (dividing nanoseconds by 1e6 and not taking a remainder)
    for line in &lines {
        for tok in line.split([' ', '(', ')', ',']) {
            if let Some((k, v)) = tok.split_once('=') {
                if k.ends_with("_ms") || k == "repair" || k == "search" {
                    let ms: f64 = v.parse().unwrap_or_else(|_| panic!("{tok} in {line}"));
                    assert!((0.0..1000.0).contains(&ms), "{tok} in {line}");
                    assert_eq!(v.split('.').nth(1).map(str::len), Some(1), "{tok}");
                }
            }
        }
    }
}

#[test]
fn rz3_stats_counts_are_the_solver_counters() {
    // sat_int: x > 3 and x < 5, two atoms, one check
    let o = run_env("sat_int", &[("RZ3_STATS", "1")]);
    assert!(o.stderr.contains(" check_calls=1 "), "{}", o.stderr);
    assert!(o.stderr.contains(" atoms=2 "), "{}", o.stderr);
    // two check-sats on the same solver
    let o = run_env("push_pop", &[("RZ3_STATS", "1")]);
    assert!(o.stderr.contains(" check_calls=5 "), "{}", o.stderr);
}

#[test]
fn rz3_stats_reports_why_the_answer_is_unknown() {
    let o = run_env("unknown_nonlinear", &[("RZ3_STATS", "1")]);
    assert_eq!(o.stdout, "unknown\n");
    let last = o.stderr.lines().last().unwrap();
    assert!(last.starts_with("stats: unknown_reason="), "{}", o.stderr);
    let o = run_env("unknown_quantifier", &[("RZ3_STATS", "1")]);
    assert_eq!(
        o.stderr.lines().last(),
        Some("stats: unknown_reason=quantifiers incomplete")
    );
}

#[test]
fn rz3_stats_has_no_unknown_reason_for_a_decided_problem() {
    let o = run_env("unsat_int", &[("RZ3_STATS", "1")]);
    assert!(!o.stderr.contains("unknown_reason"), "{}", o.stderr);
}

#[test]
fn rz3_stats_is_silent_on_a_parse_error() {
    // the error exit happens before the statistics are printed
    let o = run_env("syntax_error_truncated", &[("RZ3_STATS", "1")]);
    assert_eq!(o.stderr, "");
    assert_eq!(o.code, Some(1));
}

#[test]
fn rz3_stats_presence_not_value_enables_it() {
    let o = run_env("sat_int", &[("RZ3_STATS", "")]);
    assert!(o.stderr.starts_with("stats: "), "{}", o.stderr);
}

#[test]
fn rz3_deadline_ms_is_accepted_and_garbage_is_ignored() {
    assert_eq!(
        run_env("sat_int", &[("RZ3_DEADLINE_MS", "60000")]).stdout,
        "sat\n"
    );
    let o = run_env("unsat_int", &[("RZ3_DEADLINE_MS", "not-a-number")]);
    assert_eq!(o.stdout, "unsat\n");
    assert_eq!(o.stderr, "");
}
