//! Ring normalisation of bit-vector terms (Z/2^w). Every expected verdict below was
//! cross-checked against Z3 (`z3 -smt2`) on the identical script.
use rz3::driver::check_script;
use rz3::SolverResult;

/// (width, assertion body, expected verdict). The body is asserted as written.
const CASES: &[(usize, &str, SolverResult)] = &[
    // Distributivity, the motivating case.
    (8, "(not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z))))", SolverResult::Unsat),
    (64, "(not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z))))", SolverResult::Unsat),
    // Wrap-around: x + (-x) = 0, x - x = 0, -(-x) = x, x * 0 = 0.
    (8, "(not (= (bvadd x (bvneg x)) (_ bv0 8)))", SolverResult::Unsat),
    (8, "(not (= (bvsub x x) (_ bv0 8)))", SolverResult::Unsat),
    (8, "(not (= (bvneg (bvneg x)) x))", SolverResult::Unsat),
    (8, "(not (= (bvmul x (_ bv0 8)) (_ bv0 8)))", SolverResult::Unsat),
    // Overflow of constants: 200 + 100 = 44 mod 256; 16 * 16 = 0 mod 256.
    (8, "(not (= (bvadd (_ bv200 8) (_ bv100 8)) (_ bv44 8)))", SolverResult::Unsat),
    (8, "(not (= (bvmul (_ bv16 8) (_ bv16 8)) (_ bv0 8)))", SolverResult::Unsat),
    (8, "(not (= (bvmul x (_ bv255 8)) (bvneg x)))", SolverResult::Unsat),
    (8, "(not (= (bvadd x (_ bv255 8)) (bvsub x (_ bv1 8))))", SolverResult::Unsat),
    // Non-identities must stay satisfiable.
    (8, "(not (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) z)))", SolverResult::Sat),
    (8, "(not (= (bvadd x (_ bv1 8)) x))", SolverResult::Sat),
    (8, "(= (bvadd x (_ bv1 8)) x)", SolverResult::Unsat),
    (8, "(not (= (bvmul x x) x))", SolverResult::Sat),
    (8, "(not (= (bvmul x y) (bvmul y x)))", SolverResult::Unsat),
    // 2^(w-1) * x * (x+1) = 0 holds but is not a ring identity over Z: must still be correct.
    (4, "(not (= (bvmul (_ bv8 4) (bvmul x (bvadd x (_ bv1 4)))) (_ bv0 4)))", SolverResult::Unsat),
    (4, "(not (= (bvmul (_ bv8 4) x) (_ bv0 4)))", SolverResult::Sat),
    // Width 1: addition is xor, multiplication is and, -x = x.
    (1, "(not (= (bvneg x) x))", SolverResult::Unsat),
    (1, "(not (= (bvadd x x) (_ bv0 1)))", SolverResult::Unsat),
    (1, "(not (= (bvmul x x) x))", SolverResult::Unsat),
    (1, "(not (= (bvadd x (_ bv1 1)) (bvnot x)))", SolverResult::Unsat),
    (1, "(not (= (bvadd x y) (bvxor x y)))", SolverResult::Unsat),
    (1, "(not (= (bvadd x y) (bvor x y)))", SolverResult::Sat),
    // Opaque atoms: non-ring operators are compared structurally.
    (8, "(not (= (bvadd (bvand x y) (bvand x y)) (bvmul (_ bv2 8) (bvand x y))))", SolverResult::Unsat),
    (8, "(not (= (bvadd (bvand x y) z) (bvadd z (bvand y x))))", SolverResult::Unsat),
    (8, "(not (= (bvadd (bvand x y) z) (bvadd z (bvor x y))))", SolverResult::Sat),
    (8, "(not (= (bvmul (bvlshr x (_ bv1 8)) (bvadd y z)) (bvadd (bvmul (bvlshr x (_ bv1 8)) y) (bvmul (bvlshr x (_ bv1 8)) z))))", SolverResult::Unsat),
    (8, "(not (= (bvlshr x (_ bv1 8)) (bvlshr x (_ bv2 8))))", SolverResult::Sat),
    // Rewriting must also work under a conjunction/disjunction/ite.
    (8, "(and (= (bvmul x (bvadd y z)) (bvadd (bvmul x y) (bvmul x z))) (not (= x x)))", SolverResult::Unsat),
    (8, "(or (not (= (bvsub x y) (bvadd x (bvneg y)))) (= x (bvadd y (_ bv1 8))))", SolverResult::Sat),
    // Large constants and widths beyond 64 bits.
    (70, "(not (= (bvadd (_ bv1180591620717411303423 70) (_ bv1 70)) (_ bv0 70)))", SolverResult::Unsat),
    (70, "(not (= (bvadd (_ bv1180591620717411303423 70) (_ bv2 70)) (_ bv1 70)))", SolverResult::Unsat),
    (70, "(not (= (bvmul x (bvadd y (_ bv590295810358705651712 70))) (bvadd (bvmul x y) (bvmul x (_ bv590295810358705651712 70)))))", SolverResult::Unsat),
    (70, "(not (= (bvmul (_ bv1180591620717411303423 70) (_ bv1180591620717411303423 70)) (_ bv1 70)))", SolverResult::Unsat),
    (70, "(not (= (bvneg (_ bv1 70)) (_ bv1180591620717411303423 70)))", SolverResult::Unsat),
    (70, "(not (= (bvsub x y) (bvneg (bvsub y x))))", SolverResult::Unsat),
    (70, "(not (= (bvmul x y) (bvmul x (bvadd y (_ bv1 70)))))", SolverResult::Sat),
    (128, "(not (= (bvmul (bvadd x y) (bvsub x y)) (bvsub (bvmul x x) (bvmul y y))))", SolverResult::Unsat),
    (128, "(not (= (bvmul (bvadd x y) (bvadd x y)) (bvadd (bvmul x x) (bvmul y y))))", SolverResult::Sat),
];

#[test]
fn ring_cases_match_z3_verdicts() {
    for (w, body, want) in CASES {
        let script = format!(
            "(set-logic QF_BV)(declare-const x (_ BitVec {w}))(declare-const y (_ BitVec {w}))\
             (declare-const z (_ BitVec {w}))(assert {body})(check-sat)"
        );
        let got = check_script(&script)
            .expect("script must be accepted")
            .remove(0);
        assert_eq!(&got, want, "width {w}: {body}");
    }
}

#[test]
fn ring_identity_in_nested_boolean_context_is_not_over_applied() {
    // The equality is false in some models: it must not be rewritten to true.
    let s = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
             (assert (= (bvmul x y) (bvadd x y)))(check-sat)";
    assert_eq!(check_script(s).unwrap().remove(0), SolverResult::Sat);
    let s = "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
             (assert (ite (= x y) (= (bvsub x y) (_ bv1 8)) (= (bvmul x y) (bvmul y x))))(check-sat)";
    assert_eq!(check_script(s).unwrap().remove(0), SolverResult::Sat);
}
