## DEC-001 — Expansión del parser para soporte SMT-LIB 2.6
- Fecha: 2026-05-30
- Sesión: Gemini CLI
- Motivo: El parser actual es limitado y no soporta comandos básicos de SMT-LIB 2.6 como `set-option`. Para alcanzar el máximo nivel de implementación, es necesario ampliar la gramática.
- Alternativas descartadas: Utilizar un parser generator (e.g., nom) — descartado para mantener el proyecto 100% Rust sin dependencias externas pesadas y controlar totalmente el rendimiento del parser.
- Tradeoffs: Mayor complejidad manual en el manejo de estados del parser frente a la simplicidad de un generador.
- Impacto regulatorio esperado: Mejora en la trazabilidad del parsing conforme a los requisitos de SMT-LIB.
- Criterio de aceptación: Soporte completo de los comandos básicos de SMT-LIB 2.6 necesarios para benchmarks comunes.
- Aprobado por: Usuario (vía prioridad establecida).
