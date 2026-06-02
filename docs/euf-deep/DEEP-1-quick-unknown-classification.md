# DEEP-1 — Quick-unknown classification (production batch sample)

**Source:** `results/2026-06-01_2359_production_5min_full12/full_5min.sqlite`
**Definition:** `xolver_allon_verdict='unknown'` AND `xolver_allon_time_ms < 5000`

## Per-division quick-unknown counts (8 target combo logics)

| division | quick-unknowns | notes |
|---|--:|---|
| QF_AUFLIA | 0 | not in batch |
| QF_AUFNIA | **17** | **routing bug — see Class A1** |
| QF_AUFLRA | 0 | not in batch |
| QF_ALIA | 0 | not in batch |
| QF_ALRA | 0 | not in batch |
| QF_UFLIA | 0 | not in batch |
| QF_UFLRA | 0 | not in batch |
| QF_UFNIA | **315** | **NIA validate-sat floor over-active — see Class A2** |

panda14 = QF_DT/QF_UFDTNIA only; panda9 = ANIA/AUFNIA/LRA/NIRA/UFNIA/UFNRA;
other divisions weren't dispatched to the 5min sample. Local probe still
informative for those that ARE in the batch.

## Class A1 — QF_AUFNIA routing-floor (17/17 sampled)

**Symptom:** `lastUnknownReason = "LogicFeatureDetector: array feature outside array logic (declared=QF_AUFNIA)"`

**Root cause (src/api/Solver.cpp:1302-1318):**
```cpp
auto isArrayLogic = [&](const std::string& l) {
    bool base = l == "QF_AX" || l == "QF_ALIA" || ... "QF_AUFLRA";
    bool arrayNia = arrayNiaEnabled &&     // XOLVER_COMB_ARRAY_NIA env-gated
          (l == "QF_ANIA" || l == "QF_AUFNIA");
    return base || arrayNia;
};
if (features.hasArray && !isArrayLogic(logic)) return Unknown;
```

QF_AUFNIA / QF_ANIA are intrinsically array logics (the A means Array), but
the routing whitelist gates them OUT unless `XOLVER_COMB_ARRAY_NIA=1`. The
gate exists because the ANIA solver routing hits an ArrayReasoner eager-merge
hang (master's CANDFLAGS deliberately excludes COMB_ARRAY_NIA per the
`run_differential.sh` comment: "QF_ANIA 路由会卡在 ArrayReasoner 急合并").

**Verification:** locally enabled COMB_ARRAY_NIA on
`s3_srvr.blast.02_false-unreach-call.i.cil.c_0.smt2`:
- default: `unknown` (routing floor)
- `XOLVER_COMB_ARRAY_NIA=1`: timeout at 30s (ANIA hang confirmed)
- z3: sat in <10s

**Status:** Known-deferred boundary. EQNA-lane fix would require fixing the
ANIA-route ArrayReasoner hang (deep array-deep work). Not sprint-actionable
without significant array engineering. Floor stays default — sound but blocks
17 cases.

## Class A2 — QF_UFNIA NIA-floor (315 quick-unknowns)

**Symptom:** xolver returns `unknown` in <5s. No theory stats output. z3
returns sat in seconds.

**Sample case:** `QF_UFNIA/201903-Zohar-ic/int_check_bvule_bvashr0_ltr_inv_g.smt2`
- 73 lines, declares `(declare-fun pow2 (Int) Int)` etc — bit-manipulation
  encoded in integer arithmetic.
- xolver 15s: unknown
- z3: sat

**Root cause hypothesis:** `XOLVER_NIA_PP_VALIDATE_NONLINEAR_SAT`-class
floor — NIA validate-sat downgrades unconfirmed sat models to Unknown
(invariant 1 soundness for incomplete NIA). The Zohar `int_check_*` family
uses UF over integers + heavy nonlinear arith (mod, div, pow2) that NIA
cannot ground-prove.

**Status:** Sound-by-design floor. Recovery would require either:
- Track-3 UF model extraction extended to UFNIA-bit-int family (substantial)
- OR a stricter narrow-gate that lets these specific shapes through validator
  (high false-SAT risk)

Both out of WSL-safe sprint scope. Known boundary.

## Class B / C / D summary

- **B (SAT abort):** not observed in this sample — verdicts come from theory
  floor, not SAT-layer early-exit.
- **C (Theory abort, generic):** at least 1 case
  (`QF_UFNIA/20190909-CLEARSY/0015/00324.smt2`):
  `unknown-reason "Theory: unknown (no reason provided)"`
  — generic theory unknown without specific diagnostic.
- **D (other):** none distinct.

## Sprint actions

1. **Class A1 (AUFNIA routing):** boundary, defer to array-deep ANIA path fix.
2. **Class A2 (UFNIA NIA-floor):** boundary, defer to Track-3 broaden.
3. **Class C (Theory: no reason):** improve diagnostic — single line change
   (out of scope for soundness sprint).

## Conclusion

DEEP-1 surfaced 2 well-defined boundaries (A1 + A2) consistent with prior
catalogued architectural ceilings. No new sprint-actionable lever — but the
diagnostic is now precise enough to route the residual gap to specific
master decisions (enable ANIA path with new array fix; broaden NIA model
extraction; OR accept boundary).
