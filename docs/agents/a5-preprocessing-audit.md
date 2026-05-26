# A5 Preprocessing audit — round 1 (audit-vs-catalog)

Method per charter (`a5-preprocessing-strengthening.md`): mark each rule family
EXISTS-good / EXISTS-weak / MISSING vs Zolver code, `file:line`. Catalog families
taken from the charter (P0/P1/P2 lists); the fuller research report was not present
as a repo file — request it if more granular rules are needed.

## P0 — `≡`, default-on (mostly EXISTS)

| Rule | Status | Evidence |
|---|---|---|
| const-fold (arith) | EXISTS-good | `FormulaRewriter.cpp` simplifyNode Add:370 Mul:410 Sub:399 Neg:359 + rel const-eval :340; `IntDivModConstantFold.cpp`; `ToRealLiteralFold.cpp`; `UnconditionalConstantPropagation.cpp` constantFoldRec |
| const-fold (bool) | EXISTS-good | `FormulaRewriter.cpp` Not/And/Or/Implies/Xor/Ite/Eq/Distinct :218-337 |
| flatten assoc (And/Or/Add/Mul) | EXISTS-good | `expr/rewriter.cpp` installZolverRewriteRules (flatten); `FormulaRewriter.cpp` And/Or:222 Add:370 Mul:410 |
| comparison-normalization (p−q ⋈ 0, flip >/≥) | EXISTS-good | `expr/rewriter.cpp:13` (p>q→p−q>0, flip > to <); `parser/adapter.cpp:134` GT/GE flip |
| dedup / complementary / identity (∧/∨) | EXISTS-good | `FormulaRewriter.cpp:236-255` |
| ITE extraction (term + bool) | EXISTS-good | `expr/CoreIteLowerer.cpp` (Tseitin-style; fresh vars stay in formula → no converter needed) |
| n-ary distinct → pairwise | EXISTS-good | `NaryDistinctLowerer.cpp` |
| let / β-reduce | EXISTS-good | `parser/adapter.cpp:27` expandLet; define-fun inlined by parser |
| to_int/to_real/div/mod lowering | EXISTS-good | `ToIntDefinitionalLowerer`, `IntDivModLowerer` |
| **canonical operand sort (commutative)** | **WEAK** | FormulaRewriter dedups+flattens but no `std::sort` of operands → less sharing/hash-consing. Cheap `≡` fill. Low verdict leverage. |
| read-over-write / store-merge | N/A here | array rewrites live in theory/array (A3 lane), not preprocessor |
| SOM / monomial sort | N/A here | theory (`poly/`, `bit_blast/PolyBitBlaster`), not frontend |

## P1 — `↔SAT` + model converter (the payoff; MOSTLY MISSING) — **gated on missing infra**

| Rule | Status | Evidence / note |
|---|---|---|
| **model-converter / model-reconstruction infrastructure** | **MISSING (prerequisite)** | grep `modelConverter`/`reconstruct` → 0 frontend hits. Zolver never *eliminates* a user var: it keeps bindings (`UnconditionalConstantPropagation` preserves `x=c` atom) or introduces fresh vars that stay in the formula. True var-elimination (drop x, recover in model) has no mechanism. **This blocks the entire P1 tier.** |
| solve-eqs / Gaussian var-elimination | MISSING (frontend) | exact LA exists theory-side only (`presolve/IntegerLinearAlgebra.h`, `IntLinearEqualityCoreHNF.cpp` SNF) — not a frontend pass eliminating `x = t` globally. Needs converter. |
| global rigid (term) substitution | EXISTS-weak | `UnconditionalConstantPropagation` does `(= var CONST)` only; general `(= var term)` substitution MISSING. Converter-free *if* binding kept (≡), but then no dimension reduction. |
| unconstrained-value simplification | MISSING | `unconstrained` only in model-defaulting (`Solver.cpp:221,265`), not a preprocessing elimination of single-occurrence vars. Needs converter. |

## P2 — heavy / heuristic (gated)

| Rule | Status | Evidence |
|---|---|---|
| Ackermann | MISSING — likely N/A | grep=0. Zolver uses congruence-closure `EufSolver` (e-graph) → Ackermannization not needed for UF functional consistency. SKIP unless a specific gap. |
| extensionality instantiation | N/A here | array theory (A3) |
| aggressive ITE / store expansion | partially (CoreIteLowerer) | charter: blowup budget + default-post; not default-on |

## Conclusion / recommended round-2 target

- **P0 is essentially complete.** Only cheap fill = canonical operand sort (low leverage; do opportunistically).
- **The high-leverage MISSING rules (solve-eqs, unconstrained-elim) are the entire P1 tier, and they ALL require model-converter infrastructure that does not exist.** So the real first build is the **model-converter / eliminated-var reconstruction layer** (register `x ↦ t` substitutions, replay in reverse on the model, gate off under push/pop), then **solve-eqs (Gaussian linear var-elimination)** on top.
- **Panda cross-ref (local sweep summaries):** the timeout/unknown mass is concentrated in QF_LRA (769 timeout + 330 unknown / 1753) and QF_UFLRA (235 timeout / 1284) — families where dimensionality reduction via solve-eqs is the classic high-leverage win. *Measure-first caveat:* confirm a sample of those timeouts is dimensionality-bound (needs the remote files / a panda A/B) before committing the build, per the A1/A2 "no blind builds" rule.
- Gate for the P1 build: `ZOLVER_PP_SOLVE_EQS` default-OFF, double-gate (unit + 637 regression OFF+ON, 0 verdict change), **z3 differential watching the false-UNSAT direction (0 zolver=unsat & oracle=sat)** — the model-converter is exactly where a bug would silently drop a model or flip a verdict.
