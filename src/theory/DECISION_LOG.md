# Decision Log - NLA Solver

## DEC-001 — Polynomial Representation and Expression Conversion
- Fecha: 2026-05-30
- Sesión: gemini-cli
- Motivo: Enable NLA reasoning by converting SMT-LIB expressions to multivariate polynomials.
- Alternativas descartadas: Directly operating on AST nodes (too complex for non-linear reasoning).
- Tradeoffs: Memory usage for polynomial representation vs. ease of algorithmic implementation (CAD/GB).
- Impacto: Enables foundation for CAD/GB algorithms.
- Criterio de aceptación: Correct conversion of Add/Mul/Var/Int expressions to Polynomial struct.
## DEC-002 — Variable Mapping for Polynomials
- Fecha: 2026-05-30
- Sesión: gemini-cli
- Motivo: Correctly identify distinct variables in multivariate polynomials, replacing the previous placeholder indexing.
- Alternativas descartadas: Using string-based keys in Polynomial (slower, less efficient for algorithmic operations).
- Tradeoffs: Added complexity in managing the mapping vs. performance gain in CAD/GB algorithms.
- Impacto: Essential for correct multivariate polynomial operations.
- Criterio de aceptación: Variables are consistently mapped to unique indices within a single solver session.
- Aprobado por: Automonous Agent.

