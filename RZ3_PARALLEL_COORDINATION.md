# r-z3 — Coordinación de trabajo PARALELO (Claude ⟂ codex)

**Decisión (Frank, 2026-06-07):** R-Z3 primero. **Claude = Nivel A**, **codex = Nivel B**, **Gemini = auditor**.
Repos: r-z3 es UN crate → para paralelizar sin destruir trabajo, este documento define límites, contrato e invariantes. **Léelo antes de tocar nada.**

---

## 0. Modelo de ramas (git)
- `master` = **baseline** (incluye Fases 0+1 ya hechas: determinismo de iteración + arnés de tests).
- Claude trabaja en `level-a`.
- codex trabaja en `level-b-fp` (M5) y `level-b-mbqi` (M4). **M6 NO se empieza hasta que `level-a` aterrice M3** (ver §4).
- Merge a `master` solo con la suite **verde** y el **arnés de determinismo intacto**.

## 1. INVARIANTE DE DETERMINISMO (obligatorio para TODOS)
Frank: *eliminar todo lo no-determinista y las aproximaciones.* Reglas duras:
1. **PROHIBIDO `std::collections::HashMap`/`HashSet`** → usar `BTreeMap`/`BTreeSet` (claves ya son `Ord`). Toda la Fase 1 lo eliminó; no reintroducir.
2. **PROHIBIDO `rand`, `thread_rng`, aleatorización, barajado.**
3. **PROHIBIDO punto flotante `f64`/`f32` en lógica de decisión o valores de modelo** → aritmética exacta (`num_rational::BigRational` / `Ratio`, `num_bigint::BigInt`).
4. **PROHIBIDAS comparaciones aproximadas** (`(a-b).abs() < epsilon`) → igualdad exacta `==` sobre racionales.
5. Cualquier desempate (VSIDS, selección de variable, orden de lemas) debe ser **determinista** (p.ej. por índice).
6. **Portfolio/paralelismo (M6): prohibido salvo seeding determinista reproducible.** Por defecto, diferido.
7. El arnés `tests/determinism_full_test.rs` debe seguir **verde** (corre cada query 30× y exige resultado+modelo idénticos). Si tu cambio lo rompe, está mal.

## 2. Mapa de propiedad de archivos (para evitar conflictos)
| Archivo | Dueño | Notas |
|---|---|---|
| `ast/mod.rs` (incl. `ModelValue`, tipos) | **Claude (A)** | Contrato `ModelValue` (§3). codex NO lo edita; consume. |
| `sat/mod.rs` | **Claude (A)** hasta M3; luego abierto a M6 | M6 (in-processing/portfolio) **espera** a que M3 aterrice. |
| `lib.rs` (orquestación/get_model) | **Claude (A)** | codex coordina cambios de dispatch vía PR pequeño. |
| `theory/lra.rs`, `theory/bv.rs`, `theory/string.rs`, `theory/euf.rs`, `theory/array.rs`, `theory/nla.rs` | **Claude (A)** | completar/sanear teorías existentes. |
| `theory/quantifier.rs` + lógica MBQI | **codex (M4)** | depende de `get_model` exacto (§4). |
| `theory/fp.rs` (NUEVO) + dispatch FP en parser/lib | **codex (M5)** | módulo nuevo; mínimo solape. |
| `tactic.rs`, `proof/*` | compartido | cambios pequeños, avisar. |

## 3. CONTRATO CONGELADO: `ModelValue` (lo aterriza Claude primero en `level-a`)
**codex programa M4/M5 contra esta forma final** (no contra el `f64` actual):
```rust
pub enum ModelValue {
    Bool(bool),
    Int(i64),                  // (futuro: BigInt si hace falta)
    Real(num_rational::BigRational),  // EXACTO — reemplaza Real(f64)
    BitVec(u64, usize),
}
```
- `get_model(&self) -> BTreeMap<String, ModelValue>` (firma estable).
- Comparación de `Real` = `==` exacta (sin epsilon).
- `TheorySolver::get_model_value(&self, &Expr) -> Option<ModelValue>` (firma estable).
- **Claude commitea este cambio en `level-a` ANTES de que codex empiece M4/M5**; codex rebasa sobre ese commit.

## 4. Dependencias y secuencia
- **M5 (FP)**: módulo nuevo `theory/fp.rs`. Necesita: contrato `ModelValue` (§3) congelado. Puede arrancar en cuanto Claude commitee §3. Mínimo solape → el más paralelizable.
- **M4 (MBQI)**: necesita `get_model` **exacto y completo de todas las teorías** — eso lo entrega Nivel A (M2 ModelValue + M3 BV/teorías). codex puede ir preparando el evaluador/instanciador, pero la integración final espera el get_model exacto.
- **M6 (industrial: arenas/in-processing/portfolio)**: toca `sat/mod.rs` → **espera a M3** (determinismo SAT de Claude) para no chocar y para no reintroducir no-determinismo (portfolio).

## 5. Nivel A — lo que hace Claude (orden)
M2: (a) contrato `ModelValue` exacto + matar aproximaciones (1e-6, f64) → (b) fix string theory (lemma→SAT) → (c) pivoteo Simplex LRA → (d) inferencia de tipos App/Select.
M3: determinismo SAT (VSIDS/restart/polaridad) + BV real (quitar placeholder) + ampliar arnés.

## 6. Checklist de merge (cualquier rama → master)
- [ ] `cargo build` exit 0, **0 warnings**.
- [ ] `cargo test` verde (incl. `determinism_full_test`).
- [ ] grep `HashMap|HashSet|rand|f64|f32|< *1e-` en tu diff = 0 (salvo justificado y aprobado).
- [ ] Sin tocar archivos fuera de tu propiedad (§2) sin avisar.
