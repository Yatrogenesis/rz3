//! Regression tests for the "silent weakening" defects found by the 2026-10 pilot
//! benchmark: every case goes through the text path (strict parser -> solver) and
//! compares against the verdict an independent solver (Z3 5.1.0) gives.
//!
//! `Unk` rows are cases RZ3 may legitimately decline; the invariant under test is
//! that it never answers the *opposite* of the truth and never answers from a
//! script it only partly understood.

use rz3::driver::check_script;
use rz3::SolverResult;

#[derive(Debug, Clone, Copy, PartialEq)]
enum Want {
    Sat,
    Unsat,
    /// Truth is unsat; `unknown` or an explicit error are acceptable, `sat` is not.
    UnsatOrDecline,
    /// Truth is sat; `unknown` or an explicit error are acceptable, `unsat` is not.
    SatOrDecline,
    /// A parse/unsupported error is required (no verdict at all).
    Error,
}

const HEAD: &str = "(set-logic ALL)(declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)\
(declare-fun x () Real)(declare-fun y () Real)(declare-fun p () (_ BitVec 8))(declare-fun q () (_ BitVec 8))\
(declare-fun m () Bool)(declare-fun n () Bool)(declare-fun f (Int) Int)(declare-fun pr (Int) Bool)";

fn verdict(body: &str) -> Result<SolverResult, String> {
    let script = format!("{HEAD}{body}(check-sat)");
    check_script(&script).map(|mut v| v.remove(0))
}

fn check(name: &str, body: &str, want: Want) -> Option<String> {
    let got = verdict(body);
    let ok = matches!(
        (want, &got),
        (Want::Sat, Ok(SolverResult::Sat))
            | (Want::Unsat, Ok(SolverResult::Unsat))
            | (
                Want::UnsatOrDecline,
                Ok(SolverResult::Unsat | SolverResult::Unknown)
            )
            | (Want::UnsatOrDecline, Err(_))
            | (
                Want::SatOrDecline,
                Ok(SolverResult::Sat | SolverResult::Unknown)
            )
            | (Want::SatOrDecline, Err(_))
            | (Want::Error, Err(_))
    );
    if ok {
        None
    } else {
        Some(format!("{name}: wanted {want:?}, got {got:?}\n    {body}"))
    }
}

#[test]
fn text_path_never_weakens_a_formula() {
    use Want::*;
    let cases: &[(&str, &str, Want)] = &[
        // difference form was turned into an unconstrained application
        ("difference chain", "(assert (<= (- a b) 0))(assert (<= (- b c) 0))(assert (> (- a c) 0))", Unsat),
        ("difference chain sat", "(assert (<= (- a b) 0))(assert (<= (- b c) 0))(assert (<= (- a c) 0))", Sat),
        ("unary minus", "(assert (> (- x) 1.0))(assert (> x 0.0))", Unsat),
        ("distinct 3-ary", "(assert (distinct a b c))(assert (= a b))", Unsat),
        ("distinct sat", "(assert (distinct a b c))", Sat),
        ("chained =", "(assert (= m n m))(assert m)(assert (not n))", Unsat),
        ("chained <=", "(assert (<= a b c))(assert (> a c))", Unsat),
        ("implication", "(assert (=> m n))(assert m)(assert (not n))", Unsat),
        ("xor", "(assert (xor m m))", Unsat),
        ("xor sat", "(assert (xor m n))(assert m)", Sat),
        // let / define-fun / declare-const used to be dropped or opaque
        ("let", "(assert (let ((y1 (+ a 1))) (and (> y1 5) (< y1 0))))", Unsat),
        // div/mod by zero are unspecified (total, uninterpreted) in SMT-LIB: never force a value
        // (found by typefuzz: `(mod 31415927 0)` was rewritten to the dividend and refuted a sat problem)
        ("mod by constant zero is free", "(assert (>= (mod 5 0) 10))", SatOrDecline),
        ("div by constant zero is free", "(assert (= (div a 0) 7))", SatOrDecline),
        ("mod by variable zero is free", "(assert (and (= c 0) (>= (mod a c) 100)))", SatOrDecline),
        // overflow predicates and reductions, exhaustively checked against Z3 for widths 3 and 4
        ("bvuaddo carry", "(assert (bvuaddo #b1100 #b0100))", Sat),
        ("bvuaddo no carry", "(assert (bvuaddo #b0100 #b0010))", Unsat),
        ("bvsaddo overflow", "(assert (bvsaddo #b0100 #b0100))", Sat),
        ("bvsaddo none", "(assert (bvsaddo #b0100 #b1100))", Unsat),
        ("bvusubo borrow", "(assert (bvusubo #b0001 #b0010))", Sat),
        ("bvssubo overflow", "(assert (bvssubo #b1000 #b0001))", Sat),
        ("bvumulo overflow", "(assert (bvumulo #b0100 #b0100))", Sat),
        ("bvsmulo none", "(assert (bvsmulo #b0011 #b1111))", Unsat),
        ("bvsdivo min over -1", "(assert (bvsdivo #b1000 #b1111))", Sat),
        ("bvnego min", "(assert (bvnego #b1000))", Sat),
        ("bvredor zero", "(assert (= (bvredor #b0000) #b1))", Unsat),
        ("bvredand ones", "(assert (= (bvredand #b1111) #b1))", Sat),
        ("bvite", "(assert (= (bvite #b1 #b0011 #b0100) #b0100))", Unsat),
        ("n-ary concat", "(assert (= (concat #b1 #b0 #b1) #b101))", Sat),
        // division by a variable: valid when the divisor is non-zero, free when it is zero
        ("div by variable", "(assert (and (> c 0) (= (div a c) 3) (= a 7)))", Sat),
        ("div by variable unsat", "(assert (and (> c 0) (= (div a c) 3) (= a 2) (>= c 1)))", Unsat),
        ("mod by variable", "(assert (and (= (mod a c) 2) (= c 3) (= a 8)))", Sat),
        ("real division by variable", "(assert (and (= (/ x y) 2.0) (= y 3.0) (= x 6.0)))", Sat),
        ("real division by variable unsat", "(assert (and (= (/ x y) 2.0) (= y 3.0) (= x 7.0)))", Unsat),
        // division by zero is a total function of its arguments (CVJ adversarial finding):
        // independent free values per occurrence made these satisfiable; Z3 and cvc5 say unsat
        ("div zero functional", "(assert (and (= c 0) (= (div a c) 3) (= (div a 0) 4)))", UnsatOrDecline),
        ("mod zero functional", "(assert (and (= (mod a 0) (+ a 1)) (= (mod a 0) a)))", UnsatOrDecline),
        ("real div zero functional", "(assert (and (= y 0.0) (= (/ x y) 1.0) (= (/ x 0.0) 2.0)))", UnsatOrDecline),
        // let values that are large are named by a fresh constant instead of being copied at each use
        ("nested lets share", "(assert (let ((u (+ a a a a a a a a a a a a a a a a a a a a a a a a a a))) (let ((w (+ u u u u u u u u u u u u u u u u u u u u u u u u u u u u))) (and (> w 5) (< u 0) (> a 0)))))", Unsat),
        ("nested lets sat", "(assert (let ((u (+ a a a a a a a a a a a a a a a a a a a a a a a a a a))) (let ((w (+ u u u u u u u u u u u u u u u u u u u u u u u u u u u u))) (and (> w 5) (> a 0)))))", Sat),
        ("let of uf application", "(assert (let ((u (f (+ a a a a a a a a a a a a a a a a a a a a a a a a a a)))) (and (> u 3) (< u 2))))", Unsat),
        // ill-typed or ill-placed input is rejected, as Z3 and cvc5 do (agy audit)
        ("bvite width mismatch", "(assert (= (bvite #b1 #b0011 #b01010101) #b0011))", Error),
        ("bvuaddo width mismatch", "(assert (bvuaddo #b0011 #b01010101))", Error),
        ("named under quantifier", "(assert (forall ((z Int)) (! (> z 0) :named nq)))", Error),
        ("mod nonzero range", "(assert (< (mod a 3) 0))", Unsat),
        ("mod by zero is a function", "(assert (and (= (mod a 0) 1) (= (mod a 0) 2)))", Unsat),
        ("let shadowing", "(assert (let ((a 1)) (let ((a 2)) (= a 3))))", Unsat),
        ("define-fun constant", "(define-fun k () Int 5)(assert (> k 10))", Unsat),
        ("define-fun with parameter", "(define-fun dbl ((u Int)) Int (+ u u))(assert (= (dbl a) 7))", Unsat),
        ("define-fun sat", "(define-fun dbl ((u Int)) Int (+ u u))(assert (= (dbl a) 8))(assert (= a 4))", Sat),
        ("declare-const", "(declare-const z Int)(assert (> z 1))(assert (< z 0))", Unsat),
        // hex / binary literals
        ("hex literal", "(assert (= p #xff))(assert (= p #x00))", Unsat),
        ("hex literal sat", "(assert (= p #xff))(assert (= q (bvadd p #x01)))(assert (= q #x00))", Sat),
        ("(_ bvN w)", "(assert (= p (_ bv255 8)))(assert (= p (_ bv0 8)))", Unsat),
        // integers
        ("integer strictness", "(assert (> a 0))(assert (< a 1))", Unsat),
        ("integer parity", "(assert (= (* 2 a) 1))", Unsat),
        ("integer difference gap", "(assert (> (- a b) 0))(assert (< (- a b) 1))", Unsat),
        ("integer sat", "(assert (> (* 2 a) 1))(assert (< (* 2 a) 3))", Sat),
        // ite / division
        ("ite arithmetic", "(assert (> (ite (> x 0.0) 1.0 2.0) 5.0))", Unsat),
        ("ite bool", "(assert (ite m n (not n)))(assert m)(assert (not n))", Unsat),
        ("division by constant", "(assert (> (/ x 2.0) 1.0))(assert (< x 1.0))", Unsat),
        // incompletely-supported theories must decline, never answer sat
        ("nonlinear", "(assert (< (* x x) 0.0))", UnsatOrDecline),
        ("division by variable", "(assert (< (/ 1.0 x) 0.0))(assert (> x 0.0))", UnsatOrDecline),
        // bit-vectors
        ("bvmul", "(assert (= (bvmul p #x02) #x01))", Unsat),
        ("bvult", "(assert (bvult p #x00))", Unsat),
        ("bvule sat", "(assert (bvule p #x00))", Sat),
        ("bvugt", "(assert (bvugt p #xff))", Unsat),
        ("bvslt", "(assert (bvslt p #x80))", Unsat),
        ("bvsgt sat", "(assert (bvsgt p #x7f))", Unsat),
        ("bvshl", "(assert (= (bvshl p #x01) #x01))", Unsat),
        ("bvshl by width", "(assert (= p #x01))(assert (not (= (bvshl p #x08) #x00)))", Unsat),
        ("bvlshr", "(assert (= p #x80))(assert (not (= (bvlshr p #x07) #x01)))", Unsat),
        ("bvashr", "(assert (= p #x80))(assert (not (= (bvashr p #x07) #xff)))", Unsat),
        ("bvsub", "(assert (= p #x00))(assert (not (= (bvsub p #x01) #xff)))", Unsat),
        ("bvand/or/xor", "(assert (= p #xaa))(assert (not (= (bvxor p (bvand p #x0f)) #xa0)))", Unsat),
        ("bvnot", "(assert (= p #x0f))(assert (not (= (bvnot p) #xf0)))", Unsat),
        ("extract/concat", "(assert (= p #xa5))(assert (not (= (concat ((_ extract 3 0) p) ((_ extract 7 4) p)) #x5a)))", Unsat),
        ("bv ite", "(assert (= p (ite m #x01 #x02)))(assert (= p #x03))", Unsat),
        // equations that an old tactic dropped
        ("conflicting definitions", "(assert (and (= a 1) (= a 2)))", Unsat),
        ("cyclic definitions", "(assert (and (= a (+ b 1)) (= b (+ a 1))))", Unsat),
        // uninterpreted functions with arithmetic arguments
        ("congruence over arithmetic", "(assert (= a b))(assert (not (= (f (+ a 1)) (f (+ b 1)))))", Unsat),
        ("predicate congruence", "(assert (= a b))(assert (pr (+ a 1)))(assert (not (pr (+ b 1))))", Unsat),
        ("function sat", "(assert (not (= (f a) (f b))))", Sat),
        ("distinct on applications", "(assert (distinct (f a) (f b) (f c)))(assert (= a b))", Unsat),
        // constant folding must not wrap around i64
        ("i64 overflow in +", "(assert (> (+ 9223372036854775807 1) 0))", Sat),
        ("i64 overflow in + twice", "(assert (> (+ 9223372036854775807 9223372036854775807) 0))", Sat),
        ("i64 overflow in *", "(assert (> (* 4611686018427387904 2) 0))", Sat),
        ("i64 overflow in * (square)", "(assert (> (* 3037000500 3037000500) 0))", Sat),
        ("i64 overflow in -", "(assert (< (- (- 9223372036854775807) 2) 0))", Sat),
        ("i64 overflow with variable", "(assert (> (* a 4611686018427387904 2) 0))(assert (= a 1))", Sat),
        ("tiny decimal", "(assert (= x 0.00000000000000000001))(assert (< x 0.000000000000000000005))", Unsat),
        // arbitrary-precision numerals, large and tiny
        ("huge integer bounds", "(assert (> a 99999999999999999999999999))(assert (< a 100000000000000000000000001))(assert (not (= a 100000000000000000000000000)))", Unsat),
        ("huge integer gap", "(assert (> a 99999999999999999999999999))(assert (< a 100000000000000000000000000))", Unsat),
        ("tiny rational difference", "(assert (<= (- x y) (/ 1 1000000000000000000000000000000000)))(assert (> (- x y) (/ 1 2000000000000000000000000000000011)))", Sat),
        ("tiny decimals", "(assert (< x 0.000000000000000000000000000000000000001))(assert (> x 0.000000000000000000000000000000000000002))", Unsat),
        ("huge product", "(assert (= a (* 123456789012345678901234567890 987654321098765432109876543210)))(assert (< a 0))", Unsat),
        ("long decimals", "(assert (= x 12345678901234567890.12345678901234567890))(assert (> x 12345678901234567890.123456789012345678901))", Unsat),
        ("huge negative", "(assert (> a (- 99999999999999999999999999999999)))(assert (< a (- 99999999999999999999999999999998)))", Unsat),
        // integer division family and mixed int/real operators
        ("mod range", "(assert (= (mod a 2) 5))", Unsat),
        ("div definition", "(assert (= (div a 3) 2))(assert (< a 6))", Unsat),
        ("div negative divisor", "(assert (= (div a (- 3)) 2))(assert (> a (- 4)))", Unsat),
        ("div negative divisor sat", "(assert (= (div a (- 3)) 2))(assert (> a (- 6)))", Sat),
        ("div sat", "(assert (= (div a 3) 2))(assert (= a 7))", Sat),
        ("mod identity", "(assert (not (= a (+ (* 3 (div a 3)) (mod a 3)))))", Unsat),
        ("abs", "(assert (< (abs a) 0))", Unsat),
        ("abs sat", "(assert (= (abs a) 3))(assert (< a 0))", Sat),
        ("to_int", "(assert (= (to_int x) 2))(assert (< x 2.0))", Unsat),
        ("to_int sat", "(assert (= (to_int x) 2))(assert (= x 2.5))", Sat),
        ("is_int", "(assert (is_int x))(assert (> x 0.2))(assert (< x 0.8))", Unsat),
        ("to_real", "(assert (> (to_real a) 2.5))(assert (< a 3))", Unsat),
        // numeric typing of arithmetic inside ite
        ("ite with real branches", "(assert (>= 2.7 (+ (ite false (+ (- 2.0) x) (+ (- 4.0) 5.9)) 0.8)))", Sat),
        ("ite real then int", "(assert (= (ite m 1 2.5) 2.5))(assert m)", Unsat),
        // bit-vector operators added after the pilot
        ("bvneg", "(assert (= p #x05))(assert (not (= (bvneg p) #xfb)))", Unsat),
        ("bvudiv", "(assert (= p #x64))(assert (not (= (bvudiv p #x07) #x0e)))", Unsat),
        ("bvudiv by zero", "(assert (not (= (bvudiv p #x00) #xff)))", Unsat),
        ("bvurem by zero", "(assert (= p #x2a))(assert (not (= (bvurem p #x00) #x2a)))", Unsat),
        ("bvsdiv", "(assert (= p #xf6))(assert (not (= (bvsdiv p #x03) #xfd)))", Unsat),
        ("bvsrem", "(assert (= p #xf6))(assert (not (= (bvsrem p #x03) #xff)))", Unsat),
        ("bvsmod", "(assert (= p #xf6))(assert (not (= (bvsmod p #x03) #x02)))", Unsat),
        ("zero_extend", "(assert (= p #xff))(assert (not (= ((_ extract 11 8) ((_ zero_extend 4) p)) #x0)))", Unsat),
        ("sign_extend", "(assert (= p #xff))(assert (not (= ((_ extract 11 8) ((_ sign_extend 4) p)) #xf)))", Unsat),
        ("rotate_left", "(assert (= p #x81))(assert (not (= ((_ rotate_left 1) p) #x03)))", Unsat),
        ("rotate_right", "(assert (= p #x81))(assert (not (= ((_ rotate_right 1) p) #xc0)))", Unsat),
        ("rotate beyond width", "(assert (= p #x81))(assert (not (= ((_ rotate_left 9) p) #x03)))", Unsat),
        ("repeat", "(assert (= p #xa5))(assert (not (= ((_ extract 15 8) ((_ repeat 2) p)) #xa5)))", Unsat),
        ("bvnand", "(assert (= p #xf0))(assert (not (= (bvnand p #x3c) #xcf)))", Unsat),
        ("bvcomp", "(assert (= p q))(assert (not (= (bvcomp p q) #b1)))", Unsat),
        // quantifiers: an existential is not a free Boolean
        ("exists with a false body", "(assert (exists ((q Int)) (> (* 2 0) 0)))", Unsat),
        ("exists needs a witness", "(assert (exists ((q Int)) (and (> q a) (< q a))))", Unsat),
        ("exists satisfiable", "(assert (exists ((q Int)) (> q a)))", SatOrDecline),
        ("not forall is exists", "(assert (not (forall ((q Int)) (> q a))))", SatOrDecline),
        ("negated exists is forall", "(assert (not (exists ((q Int)) (> q 0))))(assert (> a 0))", Unsat),
        ("forall instantiation refutes", "(assert (forall ((q Int)) (> (f q) q)))(assert (<= (f a) a))", Unsat),
        ("exists under forall", "(assert (forall ((q Int)) (exists ((r Int)) (> r q))))", SatOrDecline),
        ("forall exists contradiction", "(assert (exists ((q Int)) (forall ((r Int)) (and (> (f a) 0) (>= (+ q r) 1)))))", UnsatOrDecline),
        // front end must reject, not guess
        ("error inside the last command", "(assert (> a 0))(check-sat ')", Error),
        ("undeclared symbol", "(assert (> zz 1))", Error),
        ("undeclared operator", "(assert (> (foo a) 1))", Error),
        ("unknown command", "(echo \"x\")(declare-datatypes ())", Error),
        ("bit-vector wider than 64", "(declare-fun w () (_ BitVec 128))(assert (= w w))", Error),
        ("wrong arity", "(assert (= (f a b) 1))", Error),
        ("malformed let", "(assert (let ((a)) true))", Error),
        ("unbalanced input", "(assert (> a 0)", Error),
    ];
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|(name, body, want)| check(name, body, *want))
        .collect();
    assert!(
        failures.is_empty(),
        "{} failure(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn partial_scripts_never_yield_a_verdict() {
    // The old CLI stopped at the first command it could not parse and then answered
    // `sat` for the prefix it had read.
    for script in [
        "(declare-fun a () Int)(assert (> a 1))(get-info :name)(foo)(assert (< a 0))(check-sat)",
        "(declare-fun a () Int)(assert (> a 1))(assert (< a 0)",
        "(declare-fun a () Int)(assert (> a 1)) # (assert (< a 0))(check-sat)",
    ] {
        assert!(check_script(script).is_err(), "must be an error: {script}");
    }
}

#[test]
fn incremental_scopes_agree_with_truth() {
    let script = "(declare-fun a () Int)(assert (> a 0))(push 1)(assert (< a 1))(check-sat)(pop 1)\
(check-sat)(push 1)(assert (> a 5))(check-sat)(pop 1)(check-sat)";
    let got = check_script(script).unwrap();
    assert_eq!(
        got,
        vec![
            SolverResult::Unsat,
            SolverResult::Sat,
            SolverResult::Sat,
            SolverResult::Sat
        ]
    );
}

#[test]
fn verdicts_are_deterministic() {
    let body = "(assert (or (and (distinct a b c) (> (- b a) 0)) (not (distinct a b c))))\
(assert (= (f a) (f c)))(assert (bvult p q))(assert (> (* 3 a) b))";
    let first = format!("{:?}", verdict(body));
    for _ in 0..30 {
        assert_eq!(format!("{:?}", verdict(body)), first);
    }
}

const SORT_HEAD: &str = "(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)(declare-fun c () U)(declare-fun d () U)\
(declare-fun f (U) U)(declare-fun g (U U) U)(declare-fun p (U) Bool)(declare-fun m () Bool)";

#[test]
fn uninterpreted_sorts_agree_with_the_standard() {
    use Want::*;
    let cases: &[(&str, &str, Want)] = &[
        (
            "transitivity",
            "(assert (= a b))(assert (= b c))(assert (not (= a c)))",
            Unsat,
        ),
        (
            "congruence",
            "(assert (= a b))(assert (not (= (f a) (f b))))",
            Unsat,
        ),
        (
            "nested congruence",
            "(assert (= a b))(assert (not (= (f (f a)) (f (f b)))))",
            Unsat,
        ),
        (
            "binary congruence",
            "(assert (= a b))(assert (= c d))(assert (not (= (g a c) (g b d))))",
            Unsat,
        ),
        (
            "no spurious congruence",
            "(assert (not (= (f a) (f b))))",
            Sat,
        ),
        (
            "predicate congruence",
            "(assert (= a b))(assert (p a))(assert (not (p b)))",
            Unsat,
        ),
        ("predicate sat", "(assert (p a))(assert (not (p b)))", Sat),
        (
            "distinct",
            "(assert (distinct a b c))(assert (= a c))",
            Unsat,
        ),
        ("distinct sat", "(assert (distinct a b c d))", Sat),
        (
            "diamond chain",
            "(assert (= a b))(assert (= b c))(assert (= c d))(assert (not (= (f a) (f d))))",
            Unsat,
        ),
        (
            "ite over sorts",
            "(assert (= (ite m a b) c))(assert m)(assert (not (= a c)))",
            Unsat,
        ),
        (
            "ite sat",
            "(assert (= (ite m a b) c))(assert (not m))(assert (not (= a c)))",
            Sat,
        ),
        (
            "propagation through congruence",
            "(assert (= (f a) b))(assert (= a (f a)))(assert (not (= (f (f a)) b)))",
            Unsat,
        ),
        (
            "disjunction",
            "(assert (or (= a b) (= a c)))(assert (not (= a b)))(assert (not (= a c)))",
            Unsat,
        ),
    ];
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|(name, body, want)| {
            let script = format!("{SORT_HEAD}{body}(check-sat)");
            let got = check_script(&script).map(|mut v| v.remove(0));
            let ok = matches!(
                (want, &got),
                (Want::Sat, Ok(SolverResult::Sat)) | (Want::Unsat, Ok(SolverResult::Unsat))
            );
            if ok {
                None
            } else {
                Some(format!("{name}: wanted {want:?}, got {got:?}"))
            }
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

const ARRAY_HEAD: &str = "(set-logic QF_ALIA)(declare-fun A () (Array Int Int))(declare-fun B () (Array Int Int))(declare-fun C () (Array Int Int))\
(declare-fun i () Int)(declare-fun j () Int)(declare-fun k () Int)(declare-fun v () Int)(declare-fun m () Bool)";

#[test]
fn arrays_agree_with_the_standard() {
    use Want::*;
    let cases: &[(&str, &str, Want)] = &[
        ("read over write same index", "(assert (not (= (select (store A i v) i) v)))", Unsat),
        ("read over write other index", "(assert (not (= i j)))(assert (not (= (select (store A i v) j) (select A j))))", Unsat),
        ("read over write sat", "(assert (= (select (store A i v) j) 5))(assert (not (= (select A j) 5)))", Sat),
        ("store twice", "(assert (not (= (select (store (store A i 1) j 2) i) 1)))(assert (not (= i j)))", Unsat),
        ("extensionality", "(assert (not (= A B)))(assert (= (select A i) (select B i)))(assert (= (select A j) (select B j)))", Sat),
        ("extensionality forces witness", "(assert (not (= (store A i (select A i)) A)))", Unsat),
        ("equal arrays equal reads", "(assert (= A B))(assert (not (= (select A i) (select B i))))", Unsat),
        ("congruence of select", "(assert (= i j))(assert (not (= (select A i) (select A j))))", Unsat),
        ("store identity", "(assert (not (= (store (store A i v) i v) (store A i v))))", Unsat),
        ("const array", "(assert (not (= (select ((as const (Array Int Int)) 7) i) 7)))", Unsat),
        ("const array sat", "(assert (= (select ((as const (Array Int Int)) 7) i) 7))", Sat),
        ("array ite", "(assert (= (select (ite m A B) i) 3))(assert m)(assert (not (= (select A i) 3)))", Unsat),
        ("swap", "(assert (= B (store (store A i (select A j)) j (select A i))))(assert (not (= (select B i) (select A j))))", Unsat),
        ("swap sat", "(assert (= B (store (store A i (select A j)) j (select A i))))(assert (= (select B j) (select A i)))", Sat),
        ("arrays differ", "(assert (not (= A B)))(assert (= A C))(assert (= B C))", Unsat),
        ("constant arrays disagree on the default", "(assert (= ((as const (Array Int Int)) 2) (store (store C (+ i 2) 1) (+ i 1) 2)))(assert (= (store C (+ i 1) 2) (store ((as const (Array Int Int)) 1) (- j 1) 2)))", Unsat),
        ("integer index arithmetic", "(assert (= (select A (+ i 1)) 4))(assert (= j (+ i 1)))(assert (not (= (select A j) 4)))", Unsat),
    ];
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|(name, body, want)| {
            let script = format!("{ARRAY_HEAD}{body}(check-sat)");
            let got = check_script(&script).map(|mut v| v.remove(0));
            let ok = matches!(
                (want, &got),
                (Want::Sat, Ok(SolverResult::Sat)) | (Want::Unsat, Ok(SolverResult::Unsat))
            );
            if ok {
                None
            } else {
                Some(format!("{name}: wanted {want:?}, got {got:?}"))
            }
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn named_terms_are_usable_in_later_assertions_and_in_the_same_command() {
    use Want::*;
    // Truth values from Z3 (-smt2).
    let cases: Vec<(&str, &str, Want)> = vec![
        ("named assertion reused", "(assert (! (> a 3) :named t1))(assert (< a 2))(assert t1)", Unsat),
        ("named negated", "(assert (! (> a 3) :named t1))(assert (not t1))(assert (> a 5))", Unsat),
        ("named term reused as a term", "(assert (! (> (+ a 1) 3) :named t1))(assert (= b (+ (! a :named w) 0)))(assert (not (= w b)))", Unsat),
        ("named subterm used in the same command", "(assert (= c (! (+ a 1) :named s1)))(assert (< (+ s1 0) c))", Unsat),
    ];
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|(name, body, want)| check(name, body, *want))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
