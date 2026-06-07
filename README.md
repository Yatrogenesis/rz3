# RZ3: A Standalone 100% Rust SMT Solver

RZ3 is a high-performance, native Rust SMT (Satisfiability Modulo Theories) solver. It is designed to be a lightweight, efficient, and thread-safe replacement for C++ based solvers like Z3 in Rust environments.

## Features
- **Pure Rust:** No external C dependencies.
- **CDCL SAT Solver:** A robust implementation of the Conflict-Driven Clause Learning algorithm.
- **Lazy SMT (DPLL(T)):** Efficient integration between the SAT engine and theory solvers.
- **Linear Real Arithmetic (LRA):** Support for real-valued linear constraints using an incremental Simplex algorithm.
- **SMT-LIB 2.0 Compatible:** (In progress) Native parsing of SMT-LIB 2.0 files.

## Project Structure
- `src/ast`: Representation of logical and arithmetic expressions.
- `src/sat`: CDCL-based SAT decision engine.
- `src/theory`: Specialized theory solvers (Simplex for LRA, Bit-vectors, etc.).
- `src/parser`: SMT-LIB 2.0 Lexer and Parser.

## Usage
Add RZ3 to your `Cargo.toml`:

```toml
[dependencies]
rz3 = { git = "..." }
```

## Contributing
RZ3 is an open-source project. Contributions are welcome!

## License
MIT License
