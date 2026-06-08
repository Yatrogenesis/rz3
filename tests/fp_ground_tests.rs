use rz3::ast::Expr;
use rz3::parser::Parser;
use rz3::{Rz3Solver, SolverResult};

fn fp32(sign: u64, exp: u64, sig: u64) -> Expr {
    Expr::App(
        "fp".to_string(),
        vec![
            Expr::BvConst(sign, 1),
            Expr::BvConst(exp, 8),
            Expr::BvConst(sig, 23),
        ],
    )
}

fn rne() -> Expr {
    Expr::Var("RNE".to_string(), rz3::ast::Type::Real)
}

#[test]
fn fp_ground_binary32_one_plus_one_equals_two() {
    let one = fp32(0, 0x7f, 0);
    let two = fp32(0, 0x80, 0);
    let add = Expr::App("fp.add".to_string(), vec![rne(), one.clone(), one]);
    let diseq = Expr::Not(Box::new(Expr::Eq(Box::new(add), Box::new(two))));

    let mut solver = Rz3Solver::new();
    solver.assert(&diseq);
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn fp_ground_binary32_inf_plus_neg_inf_is_nan() {
    let pos_inf = fp32(0, 0xff, 0);
    let neg_inf = fp32(1, 0xff, 0);
    let add = Expr::App("fp.add".to_string(), vec![rne(), pos_inf, neg_inf]);
    let is_nan = Expr::App("fp.isNaN".to_string(), vec![add]);

    let mut solver = Rz3Solver::new();
    solver.assert(&is_nan);
    assert!(matches!(solver.check(), SolverResult::Sat));
}

#[test]
fn fp_ground_binary32_zero_times_inf_is_not_a_number() {
    let zero = fp32(0, 0, 0);
    let pos_inf = fp32(0, 0xff, 0);
    let mul = Expr::App("fp.mul".to_string(), vec![rne(), zero, pos_inf]);
    let not_nan = Expr::Not(Box::new(Expr::App("fp.isNaN".to_string(), vec![mul])));

    let mut solver = Rz3Solver::new();
    solver.assert(&not_nan);
    assert!(matches!(solver.check(), SolverResult::Unsat));
}

#[test]
fn parser_accepts_smtlib_binary_fp_constructor_and_operator() {
    let mut parser = Parser::new(
        "(fp.add RNE (fp #b0 #b01111111 #b00000000000000000000000) (fp #b0 #b01111111 #b00000000000000000000000))",
    );
    let expr = parser.parse_expr().unwrap();
    match expr {
        Expr::App(name, args) => {
            assert_eq!(name, "fp.add");
            assert_eq!(args.len(), 3);
        }
        other => assert!(
            matches!(other, Expr::App(_, _)),
            "expected fp.add application"
        ),
    }
}
