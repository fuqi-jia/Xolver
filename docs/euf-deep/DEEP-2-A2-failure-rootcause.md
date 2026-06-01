# DEEP-2 — A2 (XOLVER_ARRAY_CONGR_EXT) failure root-cause

## Claim under investigation

> COMB-4 reported "A2 rec=0 lost=0 → done". Master critique: investigate
> WHY rec=0, find root cause, not surface-close.

## Trigger condition (src/theory/euf/EufSolver.cpp:681-740)

A2 emits a (a = b ∨ select(a,k) ≠ select(b,k)) extensionality lemma when:
1. Two terms `h(p..)` and `h(q..)` exist with the SAME function symbol
2. They differ in EXACTLY ONE argument position
3. That differing argument is ARRAY-sorted
4. `h(p..) ≠ h(q..)` holds locally or on shared bus (egraph CLASS match)
5. User function (not internal `#` prefix — array Row1/Row2/Ext owns those)

## Why rec=0 on ALIA/AUFLIA sample

Sampled 15 ALIA/AUFLIA cases. NONE matched the trigger:
- **Pure-arith Rodin** (Frequent: 120/120 sampled AUFLIA were array-free per
  A3 telemetry). Routed by A3 NOARR_DOWNGRADE. No array args anywhere.
- **Pure array** (select/store chains). Handled by Row1/Row2/Ext. No
  user UF over Array.
- **UF over Int** (Wisa class `select_format : Int → Int`). The integer
  arg means A2's array-sortedness guard fails. COMB_VALIDATE_SAT handles
  Wisa post-hoc.

## Verification on Wisa (where master suggested A2 might help)

`QF_UFLIA/mathsat/Wisa/xs-09-13-2-3-1-3.smt2`:
- default: sat (false-SAT — known Wisa class)
- `XOLVER_ARRAY_CONGR_EXT=1`: sat (A2 doesn't fire — `select_format` is
  Int→Int, no array sort)
- `XOLVER_COMB_VALIDATE_SAT=1 XOLVER_EUF_UF_MODEL=1`: unknown
  (the correct floor for Wisa)

## Conclusion

A2's narrow niche is legitimate. The shape it targets (UF: Array → X with
diseq results) is rare in the QF_ALIA/AUFLIA corpora available. NOT a bug,
NOT a missed opportunity — just narrow.

**Adjacent niches handled by other levers:**
- Pure-arith QF_AUFLIA → A3 NOARR_DOWNGRADE (shipped default-ON)
- Pure array → Row1/Row2/Ext (built-in)
- UF over Int (Wisa) → COMB_VALIDATE_SAT (shipped, opt-in)

**Potential broadening (R&D, not sprint-actionable):**
A2 could be generalized to fire on `UF: Int → X` when the integer args
differ in arith model but coincide in EUF model — this is essentially the
model-based arrangement splitting already provided by COMB_MODEL_BASED.
Promoting / refining COMB_MODEL_BASED would cover this niche more cleanly
than broadening A2's narrow detector.

## Sprint outcome

No code change. A2 stays env-gated default-OFF — correct given narrow
niche. R&D suggestion: focus broadening on COMB_MODEL_BASED, not A2.
