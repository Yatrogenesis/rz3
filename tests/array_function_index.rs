//! A function application used as an array index. The array reducer once compared index types with
//! `Expr::get_type()`, which is `Unknown` for an application, and silently dropped the read-over-write
//! axioms for such indices: `f(i) = i /\ select(store(A, f(i), 7), i) != 7` was reported satisfiable.
//! Every verdict below was cross-checked with Z3 5.1.0 (the unsat ones also with cvc5 and Yices).
use rz3::driver::check_script;
use rz3::SolverResult;

const HEAD: &str = "(set-logic QF_AUFLIA)(declare-const A (Array Int Int))(declare-const i Int)(declare-const j Int)(declare-fun f (Int) Int)";

fn verdict(body: &str) -> SolverResult {
    check_script(&format!("{HEAD}{body}(check-sat)"))
        .unwrap()
        .remove(0)
}

#[test]
fn equal_index_through_a_function_forces_the_stored_value() {
    for body in [
        "(assert (and (= (f i) i) (distinct (select (store A (f i) 7) i) 7)))",
        "(assert (= (f i) i))(assert (distinct (select (store A (f i) 7) i) 7))",
        "(assert (distinct (select (store A (f i) 7) i) 7))(assert (= (f i) i))",
        "(assert (= (f i) j))(assert (= j i))(assert (distinct (select (store A (f i) 7) i) 7))",
        "(assert (= (f i) i))(assert (= (select (store A (f i) 7) i) 8))",
    ] {
        assert!(matches!(verdict(body), SolverResult::Unsat), "{body}");
    }
}

#[test]
fn the_same_index_term_on_both_sides_still_works() {
    assert!(matches!(
        verdict("(assert (= (f i) i))(assert (distinct (select (store A (f i) 7) (f i)) 7))"),
        SolverResult::Unsat
    ));
    assert!(matches!(
        verdict("(assert (and (= j i) (distinct (select (store A j 7) i) 7)))"),
        SolverResult::Unsat
    ));
}

#[test]
fn satisfiable_neighbours_are_not_over_constrained() {
    for body in [
        "(assert (and (= j (f i)) (= (select (store A (f i) 7) j) 7)))",
        "(assert (and (= (f i) i) (= (select (store A (f i) 7) i) 7)))",
        "(assert (and (distinct (f i) i) (= (select (store A (f i) 7) i) (select A i))))",
    ] {
        assert!(matches!(verdict(body), SolverResult::Sat), "{body}");
    }
}
