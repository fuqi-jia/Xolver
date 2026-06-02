# DEEP-5 — Algorithm idea exploration (honest negative)

Synthesizing DEEP-1..4 to surface a new sprint-actionable lever.

## Candidates considered

### A. AUFNIA ARRAY_NIA enable for "mostly arith" cases
Hypothesis: ANIA path hangs on heavy array merging, but small-array
AUFNIA cases might succeed.

Test: 3 UltimateAutomizer cases with `XOLVER_COMB_ARRAY_NIA=1` at 60s:
- s3_srvr.blast.02_false-unreach-call.i.cil.c_0.smt2: timeout
- s3_clnt.blast.01_false-unreach-call.i.cil.c_0.smt2: timeout
- s3_srvr.blast.04_false-unreach-call.i.cil.c_0.smt2: timeout

**Result:** all 3 timeout — ANIA hang affects even these. Narrow-gate doesn't
help; the hang is in early routing not bound to array size.

**Outcome:** Rejected.

### B. Wisa over-floor reduction (combinationModelDefinitelyViolates narrower)
Hypothesis: if validator's funcInterps from Track-3 have the correct
table for the assertion's queried args, validator is reliable; if NOT,
validator should return Indeterminate (not Violated).

Investigation: collectFunctionInterps (EufSolver.cpp:1862) emits entries
keyed on class tokens for every interned UFApply. The DEFAULT is empty,
which already maps to Indeterminate in the validator (ArithModelValidator.cpp:453).
So lookups for un-tabulated args ALREADY produce Indeterminate. The Violated
verdict on the 7 over-floor cases means the lookup IS finding entries but
the entry values disagree with the assertion. This is the genuine
combination unsoundness in xolver's model construction.

**Outcome:** Not validator-side; needs combination model construction fix
(post-sprint R&D — same scope as the master-noted "Wisa var-const
internal-bridge redesign").

### C. Quick-unknown diagnostic improvement (DEEP-1 Class C)
Hypothesis: `unknown-reason "Theory: unknown (no reason provided)"` could
emit a more specific reason.

Investigation: a single-line improvement for diagnostic UX. Not solver-
side improvement.

**Outcome:** Out of soundness sprint scope.

## Conclusion

DEEP-1..4 surfaced known architectural boundaries:
1. AUFNIA ANIA path (engine hang) — array-deep lane
2. UFNIA bit-int (NIA engine extension) — NIA agent lane
3. UFNRA cas/sqrtmodinv (NRA-CAC perf) — NRA agent lane
4. Wisa combination model construction — post-sprint R&D

None are sprint-actionable in EQNA's lane. The shipped DEEP-3 promotion
(COMB_VALIDATE_SAT + UF_MODEL default-on with CMS recovery) is the one
soundness win surfaced this round.

**Net DEEP cycle outcome:** 3 default-ON promotes (IFACE_LIFECYCLE,
ARRAY_NOARR_DOWNGRADE, COMB_VALIDATE_SAT+UF_MODEL) + 1 CMS recovery
extension + 5 diagnostic docs. No new algorithm; existing levers covered
the actionable surface.
