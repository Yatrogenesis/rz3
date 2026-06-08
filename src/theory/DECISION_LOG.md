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

## DEC-003 — Ground-FP IEEE-754 Integration Scope
- Fecha: 2026-06-08
- Sesión: codex
- Motivo: Integrar razonamiento FP real sin invadir el contrato AST propiedad de level-a/master.
- Alternativas descartadas: Extender `ast::Type` desde level-b (viola ownership); definir tipos FP locales en `theory::fp` (duplica contrato canonico); usar `f32`/`f64` host (rompe exactitud y determinismo bit-a-bit).
- Tradeoffs: Ground-FP queda operativo y verificable; FP con variables/modelo completo queda bloqueado hasta que el contrato canonico exponga `Type::Float` o equivalente.
- Impacto: Permite detectar conflictos FP ground con semantica IEEE-754 exacta usando `crate::ast::fp::*` y `ModelValue::Float`.
- Criterio de aceptación: `cargo test -p rz3 theory::fp -- --nocapture`, `cargo test -p rz3 --test fp_ground_tests -- --nocapture`, `cargo test --workspace --no-fail-fast`, determinismo n=30 con hash identico.
- Aprobado por: Francisco Molina Burgos (autor), bajo instruccion de no tocar ownership de `ast`.
