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
- Flag **OFF**: 632/632 PASS, 0 unsound (the non-gated validator fixes —
  by-value assignment maps + robust bool-var detection — do not regress).
- Flag **ON**: 555 PASS, **77 sat→unknown**, **0 unsound**.

Pure-boolean / linear-arith cases with complete models confirm and stay `sat`
(the gate populates boolean-variable values from the live SAT assignment). The
77 below are genuine **model-extraction incompleteness** — the verdict is
correct but the produced model cannot be positively re-validated.

## Flips by owning agent (completeness recovery)

### A3 (EUF + arrays) / A4 (combination) — no function/array interp to evaluate (42)
The validator has no UF-application or array interpretation, so any model whose
satisfaction depends on `f(...)`/`select`/`store` is Indeterminate. Recovery:
extract complete function/array interpretations into the model AND/OR extend
`ArithModelValidator` to evaluate `UFApply` against `functionInterps`.
- euf: 001, 008, 022, 024, 026, 028, 029, 042, 043, 044, 050, 052, 053, 058, 062 (15)
- uflia: 001, 005, 007, 008, 012, 014, 016, 019, 021, 023, 025 (11)
- uflra: 001(fun_real), 003, 004, 007(fn_diseq — the known a=b extraction bug), 008, 010 (6)
- ufnia: 001, 003, 004, 006, 008, divzero_001 (6)
- ufnra: 001, 003, 005, 006 (4)
- arrays: ax_010, alia_005, alra_010, auflia_004, auflra_003 (5)

### A2 (nonlinear) — algebraic-number models (20)
NRA/NIRA witnesses are real-algebraic (e.g. √2); the string assignment channel
cannot represent them losslessly, so the validator gets Indeterminate. Recovery:
forward the exact `RealValue`/algebraic witness into validation (numericAssignments).
- nra: 003, 014, 022, 036, 040, 047, 050, 057, 059, 066, 072, 093, 094, 097, 138, 140 (16)
- nira: 002, 008, 009, 023 (4)

### A1 (linear) + mixed-ite — incomplete difference-logic / mixed models (8 + 2)
IDL/RDL/LIRA models leave some variables unassigned (defaults break a difference
constraint) or to_int/ite couplings aren't reflected. Recovery: complete the
model so all original variables get consistent values.
- idl: 009, 011, 012, 015 (4)
- rdl: 007, 009, 012 (3)
- lira: 009_nonlinear_to_int (1)
- root: ite_nested_sat, uflra_001_sat_ite_mixed (2)

## Note
Each flip is a place where the verdict is right but the *printed model* would not
satisfy the original formula — i.e. exactly the Model-Validation-track soundness
risk. Fixing the model extraction (above) both removes the flip AND makes the
printed model trustworthy.
