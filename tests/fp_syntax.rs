//! Floating-point front end: every expected verdict below was cross-checked against Z3.
//! Terms the evaluator cannot decide must give `unknown`, never `sat`.
use rz3::driver::check_script;

fn verdict(body: &str) -> String {
    let script = format!("(set-logic QF_FP)\n{body}\n(check-sat)\n");
    check_script(&script)
        .map(|v| {
            v.iter()
                .map(|r| format!("{r:?}").to_lowercase())
                .collect::<Vec<_>>()
                .join(" ")
        })
        .unwrap_or_else(|e| format!("error {e}"))
}

#[test]
fn fp_cases_agree_with_z3() {
    let rows: &[(&str, &str)] = &[
        ("(assert (fp.isNaN (_ NaN 8 24)))", "sat"),
        ("(assert (= (_ NaN 8 24) (_ NaN 8 24)))", "sat"),
        ("(assert (fp.eq (_ NaN 8 24) (_ NaN 8 24)))", "unsat"),
        ("(assert (= (_ +zero 8 24) (_ -zero 8 24)))", "unsat"),
        ("(assert (fp.eq (_ +zero 8 24) (_ -zero 8 24)))", "sat"),
        ("(assert (fp.lt (_ -oo 8 24) (_ +oo 8 24)))", "sat"),
        (
            "(assert (fp.isSubnormal (fp #b0 #x00 #b00000000000000000000001)))",
            "sat",
        ),
        ("(assert (= ((_ to_fp 8 24) RNE 0.1) ((_ to_fp 8 24) #x3dcccccd)))", "sat"),
        ("(assert (= ((_ to_fp 8 24) RTZ 0.1) ((_ to_fp 8 24) #x3dcccccd)))", "unsat"),
        ("(assert (= ((_ to_fp 8 24) RTP 0.1) ((_ to_fp 8 24) #x3dcccccd)))", "sat"),
        ("(assert (= ((_ to_fp 8 24) RNE (- 1.5)) ((_ to_fp 8 24) #xbfc00000)))", "sat"),
        ("(assert (fp.isNaN (fp.min (_ NaN 8 24) (_ +zero 8 24))))", "unsat"),
        ("(assert (= (fp.max ((_ to_fp 8 24) RNE 2.0) ((_ to_fp 8 24) RNE 3.0)) ((_ to_fp 8 24) RNE 3.0)))", "sat"),
        ("(assert (= (fp.min ((_ to_fp 8 24) RNE 2.0) ((_ to_fp 8 24) RNE 3.0)) ((_ to_fp 8 24) RNE 3.0)))", "unsat"),
        // undecidable for this evaluator: must not claim sat
        ("(declare-const x Float32)(assert (fp.isNaN x))", "unknown"),
    ];
    for (body, want) in rows {
        let got = verdict(body);
        assert!(got.starts_with(want), "{body}: got {got}, want {want}");
    }
}
