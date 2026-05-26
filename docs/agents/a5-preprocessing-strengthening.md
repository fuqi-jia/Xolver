# A5 — Preprocessing / Rewriting Strengthening (task charter)

**Owner:** Agent 5 (`expr/rewriter`, `frontend/{preprocess,atomization,factory}`, `api/Solver`).
**Catalog:** the attached SMT preprocessing/rewriting research report (LIA/LRA/UF/AX/NIA/NRA/
combination, P0/P1/P2 tiers, `≡`/`↔SAT`/`Str`/`Abs+Ref` tags) is your **rule catalog**.
This charter is the **method + correctness discipline** for turning it into validated Zolver
capabilities — not a license to implement it wholesale.

## Method — audit-first, measure-first (NON-NEGOTIABLE)

The campaign has twice proven that building a perf/completeness change on an *assumption*
is wasted work (A1: the simplex was never the LRA bottleneck; A2: P3 wasn't the NRA lever —
both killed by profiling). Same rule here:

1. **Audit, don't re-implement.** For each rule family in the report, mark
   **EXISTS-good / EXISTS-weak / MISSING** against Zolver's actual code (`expr/rewriter`,
   `frontend/preprocess`, the per-theory rewriters), with `file:line` evidence — like the
   bible audits. Expect **most of P0 already exists**, and you've already shipped
   FormulaRewriter / PG-CNF / let-elim / validator-memo. Don't duplicate.
2. **Prioritize by the actual benchmark gaps, not the report's generic order.** Cross-ref the
   panda discrepancies: which *unknown/timeout* would a MISSING rule recover? If a rule won't
   move a benchmark, don't build it. (The report's priority is a prior, not the answer.)
3. **Implement the highest-leverage MISSING rules one at a time, each gated + validated.**

## Correctness discipline — the danger is FALSE-UNSAT

`ModelValidator` catches false-SAT but **NOT false-UNSAT or wrong propagation** (invariant 1).
A bad rewrite is silent unsoundness. So:

- **Tag every rule** with its semantic class and treat it accordingly:
  - `≡` (equivalence): safe, default-on candidate.
  - `↔SAT` (equisatisfiable): **MUST register a model converter** so the model is recoverable
    and incremental push/pop rolls back. Treating `↔SAT` as `≡` → wrong model / wrong
    incremental result. This covers solve-eqs, global substitution, unconstrained-elim,
    purification, Ackermann, Tseitin/PG, ITE-extraction.
  - `Str` / `Abs+Ref` (strengthening / abstract-refine): **only inside a CEGAR / refinement
    loop**, never as a blind preprocessing pass. Single-step is not equivalence.
- **Per-rule verdict gate:** regression OFF+ON with **0 verdict changes**, plus a **z3
  differential that watches the false-UNSAT direction** — `0 cases of zolver=unsat & oracle=sat`.
  That is the failure mode the validator cannot catch, so it is the gate (same gate A2 uses for
  the determinant/`RationalPolynomial` work).
- **Default-OFF flag (`ZOLVER_PP_*`) for everything beyond P0**, double-gated (OFF+ON: unit +
  632 regression, 0 unsound). Anonymous commits.
- **Specific traps (report risk table + campaign):**
  - **λ/quantifier capture** — rename to fresh *before* substituting (you already own this).
  - **div-by-zero** — only on the internal-total `div_total`/`mod_total` operators, never on
    SMT-LIB-visible `div`/`mod` (semantics/proof divergence).
  - **aggressive ITE / store / extensionality expansion** — blowup budget + default-*post*,
    never default-on (DAG→tree, boolean-layer blowup).
  - **incremental mode** — only roll-back-able rules / model-converter-backed passes; the strong
    global passes must be gated off under push/pop.

## Priority (only the MISSING rules)

- **P0 (`≡`, default-on):** fill gaps in const-fold / flatten / sort / read-over-write /
  store-merge / β-reduce / comparison-normalization / SOM. Likely mostly present — audit + fill.
- **P1 (`↔SAT` + model converter — highest dimension reduction):** solve-eqs / Gaussian
  elimination, global rigid substitution, unconstrained-value simplification, ITE extraction.
  **The biggest payoff** — but each one ships a model converter + passes the false-UNSAT gate.
- **P2 (heavy / heuristic, gated + measured):** Ackermann, `distinct` expansion, extensionality
  instantiation, aggressive ITE/store. Only where a benchmark gap justifies it; thresholds +
  fallback.

## Coordination (stay in lane)

- **NIA/NRA heavy nonlinear rules (linearization, cutting-planes, tangent/interval, CAD/CAC)
  do NOT go in the preprocessor** — they belong in the theory refinement loop. Route to
  A2 (NRA) / A6 (NIA bit-blast) / A7 (NIA reasoning). The preprocessor only does the *exact,
  cheap* nonlinear normalizations (monomial sort, factor, square-nonneg) + purification.
- **Bool-sort / `BoolSubtermPurifier` region** → A3/A7 own it; no dual-edit.
- Theory-local rewrites (LIA/LRA/UF/AX) that live in the per-theory rewriters → coordinate with
  the owning agent if outside your frontend.

## Deliverable (per round)

Gap-analysis table (rule → EXISTS-good/weak/MISSING, `file:line`) + implemented rules (flag,
semantic tag, gate result) + measured benchmark effect (which unknown/timeout recovered).
Default-OFF, double-gated, false-UNSAT-differential clean.
