# r-z3 — Plan de Fases: Determinismo + Eliminación de Aproximaciones

**Objetivo (mandato Frank):** eliminar TODO lo no-determinista y las aproximaciones de r-z3.
**Base:** `src/` = **3.226 LOC** totales. NO hay `rand` ni paralelismo (bien). Aritmética ya usa `num_rational`/`num_bigint` exacto.

## Diagnóstico (verificado en código 2026-06-06)

| Problema | Dónde | Severidad |
|---|---|---|
| **HashMap/HashSet** (iteración no determinista, seed SipHash aleatorio) | lra.rs(22), quantifier.rs(19), euf.rs(7), array.rs(7), bv.rs(5), nla.rs(5), sat(3), ast(2), tactic(2), lib.rs(17) — **~80 usos** | 🔴 ALTA — causa raíz de salida no reproducible |
| **f64 residual** (aproximación en solver exacto) | lra.rs(3), sat(5=VSIDS), parser.rs(2), quantifier(1), theory/mod(1), ast(1) — **~13 usos** | 🟠 MEDIA |
| VSIDS / restart / polaridad sin tie-break determinista | sat/mod.rs (318 LOC) | 🟠 MEDIA |
| IEEE754 FP exacto (roadmap Fase 2) | (no implementado aún) | 🟡 futuro |

---

## FASES (cada una = unidad coherente, testeable, sin agotar tokens)

### Fase 0 — Arnés de determinismo (baseline) · ~150 LOC (mayormente test)
- Test que corre el corpus SMT **N veces** y exige salida byte-idéntica (sat/unsat + modelo).
- Extiende `tests/parser_determinism_test.rs` a solver completo.
- Identifica qué queries hoy difieren entre corridas. **Sin esto no se puede verificar el resto.**

### Fase 1 — Determinismo de iteración: HashMap/HashSet → ordenado · ~350-500 LOC, ~10 archivos
- Reemplazar `HashMap`→`BTreeMap` (claves `Ord`) o `IndexMap` (orden de inserción donde importe).
- Derivar `Ord`/`PartialOrd` en tipos de clave donde falte.
- **Es la causa raíz**: arreglarlo hace reproducible modelo y orden de resolución.
- Sub-división si excede presupuesto:
  - **1a** teorías: lra, nla, euf, array, bv (~46 usos)
  - **1b** núcleo: sat, ast, tactic, lib, quantifier (~43 usos)

### Fase 2 — Eliminar f64 residual (aproximación → exacto) · ~150-250 LOC
- Auditar los ~13 sitios `f64`. `lra.rs`(3) en solver de racionales exactos = sospechoso → `Ratio<BigInt>`.
- `parser.rs`: literales numéricos → representación exacta, no f64.
- `sat/mod.rs`(5, VSIDS activity): decidir — mantener f64 heurístico con tie-break determinista, o pasar a actividad entera.

### Fase 3 — Determinismo del núcleo SAT (CDCL) · ~200-300 LOC
- Orden de decisión VSIDS con **tie-break determinista** (por índice de variable).
- Restart **Luby/fijo** (sin azar). Polaridad con default determinista (phase-saving init estable).
- Orden de borrado de cláusulas determinista.

### Fase 4 — Teoría IEEE754 FP exacta (roadmap Fase 2) · MAYOR, diferible
- Representación FP arbitraria-precisión. Más grande; se ataca después de 0-3.

---

## Recomendación de presupuesto por sesión
- **~400-600 LOC modificadas por fase** = punto óptimo (coherente + testeable + no agota tokens).
- Pase completo de determinismo (Fases 0-3) ≈ **700-1.200 LOC de cambios** sobre las 3.226 del crate → **~3-4 sesiones**.
- Nota: la crate ENTERA es 3.226 LOC; "5.000 líneas" excede el total. El trabajo son *modificaciones* localizadas, no líneas nuevas.

## Orden sugerido
**0 → 1 (1a, 1b) → 2 → 3** → (4 aparte). Empezar por Fase 0 para tener el medidor antes de tocar lógica.
