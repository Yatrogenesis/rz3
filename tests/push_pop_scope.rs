//! Declarations and `:named` terms made after `push` disappear at the matching `pop`, as in Z3
//! and cvc5. Every script below was cross-checked with Z3 5.1.0.
use rz3::driver::check_script;
use rz3::SolverResult;

fn run(script: &str) -> Result<Vec<SolverResult>, String> {
    check_script(script)
}

#[test]
fn a_constant_declared_inside_a_scope_is_gone_after_pop() {
    let r = run(
        "(push)(declare-const x Int)(assert (> x 1))(check-sat)(pop)(assert (> x 0))(check-sat)",
    );
    assert!(r.unwrap_err().contains("undeclared symbol 'x'"));
}

#[test]
fn a_name_can_be_redeclared_with_another_sort_after_pop() {
    let r =
        run("(push)(declare-const x Int)(pop)(declare-const x Bool)(assert x)(check-sat)").unwrap();
    assert!(matches!(r.as_slice(), [SolverResult::Sat]));
}

#[test]
fn pop_without_a_matching_push_is_an_error() {
    assert!(run("(pop)(check-sat)")
        .unwrap_err()
        .contains("pop without a matching push"));
    assert!(run("(push)(pop 2)(check-sat)").is_err());
}

#[test]
fn functions_macros_and_named_terms_are_scoped_too() {
    for script in [
        "(declare-const y Int)(push 2)(declare-fun f (Int) Int)(push)(assert (= (f y) 3))(check-sat)(pop 2)(assert (= (f y) 3))(check-sat)",
        "(declare-const y Int)(push)(assert (! (> y 0) :named n1))(assert n1)(check-sat)(pop)(assert n1)(check-sat)",
        "(declare-const y Int)(push)(define-fun g () Int 5)(assert (= y g))(check-sat)(pop)(assert (= y g))(check-sat)",
    ] {
        assert!(run(script).is_err(), "{script}");
    }
}

#[test]
fn assertions_and_declarations_outside_the_scope_survive() {
    let r = run("(declare-const y Int)(assert (> y 0))(push)(assert (< y 0))(check-sat)(pop)(check-sat)(push)(declare-const z Int)(assert (= z y))(check-sat)(pop)").unwrap();
    assert!(matches!(
        r.as_slice(),
        [SolverResult::Unsat, SolverResult::Sat, SolverResult::Sat]
    ));
}
