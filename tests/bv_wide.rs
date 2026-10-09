//! Bit-vectors wider than 64 bits: literals, operators, models and fail-closed limits.
//! Expected values were computed independently (Python big integers / Z3 4.x).
use rz3::driver::check_script;
use rz3::SolverResult;

fn verdict(script: &str) -> Vec<SolverResult> {
    check_script(script).expect("script must be accepted")
}

fn one(script: &str) -> SolverResult {
    verdict(script).remove(0)
}

fn decl(w: usize) -> String {
    format!("(set-logic QF_BV)(declare-const x (_ BitVec {w}))(declare-const y (_ BitVec {w}))")
}

#[test]
fn literals_of_all_forms_agree_at_70_bits() {
    let d = decl(70);
    let v: u128 = (1u128 << 69) + 5;
    let bin = format!("#b{v:070b}");
    let hex = format!("#x{:018x}", v & ((1u128 << 68) - 1)); // 72 bits: low 68 bits of v
    assert_eq!(bin.len(), 72);
    assert_eq!(
        one(&format!(
            "{d}(assert (not (= (_ bv{v} 70) {bin})))(check-sat)"
        )),
        SolverResult::Unsat
    );
    // 72-bit hex literal: its low 70 bits equal v modulo 2^70 (bit 69 is clear in the low 68-bit mask)
    assert_eq!(
        one(&format!(
            "{d}(assert (not (= ((_ extract 67 0) {hex}) ((_ extract 67 0) {bin}))))(check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (= (_ bv{v} 70) (_ bv{} 70)))(check-sat)",
            v + 1
        )),
        SolverResult::Unsat
    );
}

#[test]
fn arithmetic_wraps_modulo_2_pow_width() {
    let d = decl(65);
    // (2^65 - 1) + 1 = 0 ; 0 - 1 = 2^65 - 1 ; (2^64) * 2 = 0
    for body in [
        "(assert (not (= (bvadd #b11111111111111111111111111111111111111111111111111111111111111111 (_ bv1 65)) (_ bv0 65))))",
        "(assert (not (= (bvsub (_ bv0 65) (_ bv1 65)) #b11111111111111111111111111111111111111111111111111111111111111111)))",
        "(assert (not (= (bvmul (_ bv18446744073709551616 65) (_ bv2 65)) (_ bv0 65))))",
        "(assert (not (= (bvneg (_ bv1 65)) #b11111111111111111111111111111111111111111111111111111111111111111)))",
    ] {
        assert_eq!(one(&format!("{d}{body}(check-sat)")), SolverResult::Unsat, "{body}");
    }
}

#[test]
fn signed_and_unsigned_order_differ_at_the_top_bit() {
    let d = decl(128);
    // 2^127 is the most negative signed value: ult against 1 is false, slt is true
    let min = "(_ bv170141183460469231731687303715884105728 128)";
    assert_eq!(
        one(&format!("{d}(assert (bvult {min} (_ bv1 128)))(check-sat)")),
        SolverResult::Unsat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (not (bvslt {min} (_ bv1 128))))(check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        one(&format!("{d}(assert (bvslt {min} (_ bv1 128)))(check-sat)")),
        SolverResult::Sat
    );
}

#[test]
fn division_by_zero_follows_smtlib_at_128_bits() {
    let d = decl(128);
    let ones = "(bvnot (_ bv0 128))";
    for body in [
        format!("(assert (not (= (bvudiv x (_ bv0 128)) {ones})))"),
        "(assert (not (= (bvurem x (_ bv0 128)) x)))".to_string(),
        "(assert (not (= (bvsrem x (_ bv0 128)) x)))".to_string(),
        "(assert (not (= (bvsmod x (_ bv0 128)) x)))".to_string(),
    ] {
        assert_eq!(
            one(&format!("{d}{body}(check-sat)")),
            SolverResult::Unsat,
            "{body}"
        );
    }
}

#[test]
fn shifts_at_and_beyond_the_width() {
    let d = decl(70);
    for body in [
        "(assert (not (= (bvshl x (_ bv70 70)) (_ bv0 70))))",
        "(assert (not (= (bvlshr x (_ bv100 70)) (_ bv0 70))))",
        "(assert (bvslt x (_ bv0 70)))(assert (not (= (bvashr x (_ bv1180591620717411303423 70)) (bvnot (_ bv0 70)))))",
    ] {
        assert_eq!(one(&format!("{d}{body}(check-sat)")), SolverResult::Unsat, "{body}");
    }
}

#[test]
fn overflow_and_reduction_operators_work_above_64_bits() {
    let d = decl(65);
    let max = "#b11111111111111111111111111111111111111111111111111111111111111111";
    assert_eq!(
        one(&format!(
            "{d}(assert (bvuaddo {max} (_ bv1 65)))(check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (bvuaddo {max} (_ bv0 65)))(check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (bvumulo (_ bv18446744073709551616 65) (_ bv2 65)))(check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (bvumulo (_ bv4294967296 65) (_ bv4294967296 65)))(check-sat)"
        )),
        SolverResult::Unsat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (bvnego (_ bv18446744073709551616 65)))(check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        one(&format!("{d}(assert (= (bvredand {max}) #b1))(check-sat)")),
        SolverResult::Sat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (= (bvredor (_ bv0 65)) #b1))(check-sat)"
        )),
        SolverResult::Unsat
    );
}

#[test]
fn multiplication_inverse_is_found_at_70_bits() {
    // x * 3 = 1 (mod 2^70) has the unique solution (2^71 + 1) / 3
    let d = decl(70);
    assert_eq!(
        one(&format!(
            "{d}(assert (= (bvmul x (_ bv3 70)) (_ bv1 70)))(check-sat)"
        )),
        SolverResult::Sat
    );
    assert_eq!(
        one(&format!(
            "{d}(assert (= (bvmul x (_ bv2 70)) (_ bv1 70)))(check-sat)"
        )),
        SolverResult::Unsat
    );
}

#[test]
fn model_prints_the_full_width() {
    use std::io::Write;
    let v: u128 = (1u128 << 69) + 5;
    let script = format!(
        "{}(assert (= x (_ bv{v} 70)))(check-sat)(get-value (x (bvadd x x)))(get-model)",
        decl(70)
    );
    let dir = std::env::temp_dir().join(format!("rz3_bv_wide_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("tmp dir");
    let path = dir.join("m.smt2");
    std::fs::File::create(&path)
        .and_then(|mut f| f.write_all(script.as_bytes()))
        .expect("write");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_rz3"))
        .arg(&path)
        .output()
        .expect("run rz3");
    let r = String::from_utf8_lossy(&out.stdout).to_string();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(r.starts_with("sat"), "{r}");
    assert!(r.contains(&format!("#b{v:070b}")), "{r}");
    // x + x wraps: 2^70 + 10 mod 2^70 = 10
    assert!(r.contains(&format!("#b{:070b}", 10)), "{r}");
}

#[test]
fn out_of_range_literals_and_huge_widths_are_errors() {
    for script in [
        "(declare-const x (_ BitVec 65))(assert (= x (_ bv36893488147419103232 65)))(check-sat)", // 2^65
        "(declare-const x (_ BitVec 5000))(assert (= x x))(check-sat)",
        "(declare-const x (_ BitVec 0))(check-sat)",
        "(assert (= #x (_ bv0 8)))(check-sat)",
    ] {
        assert!(check_script(script).is_err(), "{script}");
    }
}
