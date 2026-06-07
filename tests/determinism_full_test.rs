// Fase 0 — Arnés de determinismo de extremo a extremo (solver completo).
//
// Mandato (Frank): r-z3 debe ser 100% determinista. Tras la Fase 1
// (HashMap/HashSet -> BTreeMap/BTreeSet) la iteración ya no depende del
// seed aleatorio de SipHash. Este arnés lo VERIFICA: corre cada consulta
// N veces en instancias frescas y exige que el resultado (Sat/Unsat) y el
// modelo recuperado sean byte-idénticos en todas las corridas.

use rz3::ast::{Expr, Type};
use rz3::{Rz3Solver, SolverResult};

const RUNS: usize = 30;

fn result_tag(r: &SolverResult) -> &'static str {
    match r {
        SolverResult::Sat => "sat",
        SolverResult::Unsat => "unsat",
        SolverResult::Unknown => "unknown",
    }
}

/// Corre `build` en una instancia fresca y devuelve una huella determinista
/// del resultado + modelo (el modelo es BTreeMap, su Debug ya está ordenado).
fn fingerprint(build: &dyn Fn(&mut Rz3Solver)) -> String {
    let mut solver = Rz3Solver::new();
    build(&mut solver);
    let result = solver.check();
    let model = solver.get_model();
    format!("{}|{:?}", result_tag(&result), model)
}

/// Exige que `RUNS` corridas independientes produzcan huellas idénticas.
fn assert_deterministic(name: &str, build: &dyn Fn(&mut Rz3Solver)) {
    let first = fingerprint(build);
    for i in 1..RUNS {
        let other = fingerprint(build);
        assert_eq!(
            first, other,
            "[{name}] salida NO determinista en corrida {i}:\n  esperado: {first}\n  obtenido: {other}"
        );
    }
}

fn real(name: &str) -> Expr {
    Expr::Var(name.to_string(), Type::Real)
}

#[test]
fn det_lra_unsat() {
    // (a or (x+y<=10)) and (not a) and (x>=6) and (y>=5) -> Unsat
    assert_deterministic("lra_unsat", &|s| {
        let a = Expr::Var("a".to_string(), Type::Bool);
        let (x, y) = (real("x"), real("y"));
        let sum_le = Expr::Le(
            Box::new(Expr::Add(vec![x.clone(), y.clone()])),
            Box::new(Expr::Int(10)),
        );
        s.assert(&Expr::Or(vec![a.clone(), sum_le]));
        s.assert(&Expr::Not(Box::new(a)));
        s.assert(&Expr::Ge(Box::new(x), Box::new(Expr::Int(6))));
        s.assert(&Expr::Ge(Box::new(y), Box::new(Expr::Int(5))));
    });
}

#[test]
fn det_lra_sat_model() {
    // (x+y<=10) and (x>=2) and (y>=3) -> Sat; el modelo debe ser estable.
    assert_deterministic("lra_sat_model", &|s| {
        let (x, y) = (real("x"), real("y"));
        s.assert(&Expr::Le(
            Box::new(Expr::Add(vec![x.clone(), y.clone()])),
            Box::new(Expr::Int(10)),
        ));
        s.assert(&Expr::Ge(Box::new(x), Box::new(Expr::Int(2))));
        s.assert(&Expr::Ge(Box::new(y), Box::new(Expr::Int(3))));
    });
}

#[test]
fn det_bool_many_vars() {
    // Conjunto booleano con varias variables: el orden de decisión/propagación
    // no debe alterar el resultado ni (si Sat) el modelo recuperado.
    assert_deterministic("bool_many_vars", &|s| {
        let vars: Vec<Expr> = ["p", "q", "r", "t", "u"]
            .iter()
            .map(|n| Expr::Var(n.to_string(), Type::Bool))
            .collect();
        // (p or q) and (not p or r) and (not q or t) and (not r or not t or u)
        s.assert(&Expr::Or(vec![vars[0].clone(), vars[1].clone()]));
        s.assert(&Expr::Or(vec![
            Expr::Not(Box::new(vars[0].clone())),
            vars[2].clone(),
        ]));
        s.assert(&Expr::Or(vec![
            Expr::Not(Box::new(vars[1].clone())),
            vars[3].clone(),
        ]));
        s.assert(&Expr::Or(vec![
            Expr::Not(Box::new(vars[2].clone())),
            Expr::Not(Box::new(vars[3].clone())),
            vars[4].clone(),
        ]));
    });
}
