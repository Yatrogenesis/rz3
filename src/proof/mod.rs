use crate::ast::Expr;

// REF: [Stump et al., 2008] "StarExec: A Benchmark Management System for the SMT Community"
//      Note: Reference to LFSC (Logical Framework with Side Conditions) commonly used for SMT proofs.

#[derive(Debug, Clone)]
pub enum ProofStep {
    Assume(Expr),
    TheoryLemma(Vec<Expr>, String), // The conflict clause and the theory name
    Resolution(usize, usize),      // Reference to two previous steps
}

pub struct Proof {
    pub steps: Vec<ProofStep>,
}

impl Default for Proof {
    fn default() -> Self {
        Self::new()
    }
}

impl Proof {
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }

    pub fn add_step(&mut self, step: ProofStep) -> usize {
        let id = self.steps.len();
        self.steps.push(step);
        id
    }
}

pub mod drat;
