use crate::sat::Literal;
use std::fs::File;
use std::io::Write;

pub struct DratGenerator {
    file: File,
}

impl DratGenerator {
    pub fn new(path: &str) -> std::io::Result<Self> {
        let file = File::create(path)?;
        Ok(Self { file })
    }

    pub fn log_clause(&mut self, lits: &[Literal]) -> std::io::Result<()> {
        for lit in lits {
            write!(self.file, "{} ", lit)?;
        }
        writeln!(self.file, "0")?;
        Ok(())
    }
}
