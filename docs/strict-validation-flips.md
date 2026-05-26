# ZOLVER_PP_STRICT_VALIDATION — sat→unknown flips (Agent 5)

The strict-validation gate (`ZOLVER_PP_STRICT_VALIDATION`, default OFF) emits
`sat` only when the independent `ArithModelValidator` confirms the extracted
model `Satisfied`. An `Indeterminate` model (the validator cannot fully
evaluate it) is downgraded to `unknown` — **never trusted as sat**.

This is **sound**: the gate only ever turns sat→unknown (verified: all flips
below are `oracle=sat solver=unknown`, 0 unsound, 0 unsat affected). It is the
documented trade for closing the false-sat class (the benchmark's 475 false-SAT).
Promotion to default-on waits until model extraction lets the validator confirm
these.

## Result (632-case regression)
- Flag **OFF**: 632/632 PASS, 0 unsound.
- Flag **ON, before recovery**: 555 PASS, 77 sat→unknown, 0 unsound.
- Flag **ON, after recovery (current)**: **586 PASS, 46 sat→unknown, 0 unsound** —
  **31 flips recovered to CORRECT sat**.

## Recovery mechanism (the unknown → correct-answer layer)
Two additions turn unknown back into correct sat without ever trusting an
unconfirmed model:
1. `ArithModelValidator` now evaluates `UFApply` by table lookup against a
   function interpretation (numeric-arg tuples, matching CMS's `get_str()`
   encoding).
2. When the theory's extracted model is not positively confirmed, the strict
   gate falls back to `CandidateModelSearch` — which builds a COMPLETE numeric
   model AND function interps — then **independently re-validates** it. `sat` is
   kept only if the independent validator confirms `Satisfied`. Sound: still
   sat→unknown-only; never trusts an unconfirmed model.

Recovered (31): all of rdl(3), lira(1); most of ufnia(5/6), uflra(4/6),
uflia(6/11); idl(2/4); nira(2/4); the rational-root nra(4/16).

## Residual (46) — genuinely-hard, routed to owning agents
The 46 below cannot be confirmed by CMS+validator yet. They are the true
recovery target for the theory agents.

## Flips by owning agent (completeness recovery)

### A3 (EUF + arrays) — uninterpreted-sort UF/array, no interp CMS can build (20)
The model's satisfaction depends on `f(...)`/`select`/`store` over UNINTERPRETED
sorts (sort U), so the value isn't numeric and CMS (numeric search) cannot build
an interp. Recovery: `EufSolver::getModel` should emit a function/array
interpretation from the e-graph (eclass-rep tables); the validator already
consumes `functionInterps` (numeric) and `arrayInterps` — extend its arg/return
encoding to opaque tokens for uninterpreted sorts.
- euf (15): 001, 008, 022, 024, 026, 028, 029, 042, 043, 044, 050, 052, 053, 058, 062
- arrays (5): ax_010, alia_005, alra_010, auflia_004, auflra_003

### A2 (nonlinear) — algebraic-number witnesses (14)
NRA/NIRA witnesses are real-algebraic (e.g. √2); the string channel can't carry
them and CMS's rational search can't hit them. Recovery: forward the exact
`RealValue`/algebraic witness into the model so the validator can evaluate it.
- nra (12): 003, 014, 022, 036, 047, 057, 066, 093, 094, 097, 138, 140
- nira (2): 009, 023

### Residual numeric-UF / mixed (12) — harder cases CMS didn't solve+validate
CMS is an incomplete candidate search; these numeric-UF / mixed models aren't
found within budget. Recovery: stronger combination model extraction (A4) or a
deeper search, so the PRIMARY extracted model validates directly.
- uflia (5): 005, 019, 021, 023, 025   uflra (2): 001_fun_real, 008
- ufnia (1): divzero_001   idl (2): 009, 011
- mixed-ite (2): ite_nested_sat, uflra_001_sat_ite_mixed

## Note
Each remaining flip is a place where the verdict is right but the *printed model*
would not satisfy the original formula. Fixing the extraction both removes the
flip AND makes the printed model trustworthy. The strict gate is the sound floor;
this list is the recovery target — the destination of each is a CORRECT sat.
