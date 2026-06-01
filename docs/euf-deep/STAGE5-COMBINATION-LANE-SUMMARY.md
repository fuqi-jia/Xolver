# Stage 5 — Combination Lane Summary (agent/eqna-2)

**Branch:** `agent/eqna-2`
**Final tip:** `b4b5ca0` (this commit will bump it further with the doc)
**Date:** 2026-06-02

## 8 target divisions (combination logics)

| division | status / notes |
|---|---|
| QF_AUFLIA | A3 `XOLVER_ARRAY_NOARR_DOWNGRADE` now default-ON — pure-arith Rodin cases route to QF_LIA (sound, +15 recovered) |
| QF_AUFNIA | bottlenecked on NIA engine; corpus mostly out of scope for 5min wall |
| QF_AUFLRA | A3 covers no-UF cases; has-UF path still relies on `XOLVER_COMB_VALIDATE_SAT` floor |
| QF_ALIA   | A3 covers no-UF cases |
| QF_ALRA   | A3 covers no-UF cases |
| QF_UFLIA  | `XOLVER_COMB_VALIDATE_SAT` (default-OFF) catches Wisa false-SAT class |
| QF_UFLRA  | same as UFLIA path |
| QF_UFNIA  | `XOLVER_NIA_IFACE_LIFECYCLE` now default-ON (recovers floored interface-eq sats) |

## Combination flag matrix (post-COMB-1 / COMB-2)

| flag | default | rationale |
|---|---|---|
| `XOLVER_NIA_IFACE_LIFECYCLE` | **ON** (COMB-1, 1f2ade1→bfbf16a) | verified 0 unsound on 191 cases, +recovery direction |
| `XOLVER_ARRAY_NOARR_DOWNGRADE` | **ON** (COMB-2, b4b5ca0) | PARAMOUNT soundness — +15 recovered QF_AUFLIA / 0 regress / 0 newly-unsound |
| `XOLVER_UF_FAST_CC` | **ON** (E2/E3, e84fbe1) | ~4× EUF saturation throughput, sound by construction |
| `XOLVER_DT_VALIDATOR_STRICT` | OFF | env-gated; refined a60b3ac with `sawUnderspecified` gate; do NOT add to CANDFLAGS pending master batch re-confirmation |
| `XOLVER_COMB_VALIDATE_SAT` | OFF | Wisa false-SAT floor; requires `XOLVER_EUF_UF_MODEL=1`; over-floor risk on true-sat opaque-DT — keep opt-in |
| `XOLVER_EUF_UF_MODEL` | OFF | Track-3 UF model collection; enables COMB_VALIDATE_SAT; no harm by itself |
| `XOLVER_COMB_MODEL_BASED` | OFF | in CANDFLAGS_FULL12 (master decision) |
| `XOLVER_COMB_CAREGRAPH` | OFF | in CANDFLAGS_FULL12 (master decision) |
| `XOLVER_EUF_PROP` | OFF | in CANDFLAGS_FULL12; verified net-negative on QG-class — master decides per-division |
| `XOLVER_EUF_INCREMENTAL_PROP` | OFF | verified net-negative on QG, keep for future investigation |
| `XOLVER_EUF_PROP_DEDUP` | OFF | verified net-negative on QG |
| `XOLVER_EUF_MINLEVEL_HEAP` | OFF | array-deep B2 perf opt; not yet flipped |

## Cross-lane wins applied

- **A3 `XOLVER_ARRAY_NOARR_DOWNGRADE`** — array-deep authority, promoted default-ON by EQNA per master COMB-2.
- **A1 `XOLVER_AX_STORE_MODEL`** — array A1 commit (storecomm +21); not flipped this round (no env-gate signature found on `agent/eqna-2` HEAD; need to re-merge from array-deep tip if needed).
- **`XOLVER_AX_EXT_WITNESS_COMPLETE`** — confirmed default-ON via inverted-OFF guard (`XOLVER_AX_NO_EXT_WITNESS_COMPLETE`).

## EQNA shipped commits this campaign

| commit | win |
|---|---|
| `2e680a4` | DtModelValidator structural extraction (P0 12 false-SAT closed) |
| `2a4001f` | DT_VALIDATOR_STRICT initial |
| `1f2ade1` | NIA_IFACE_LIFECYCLE verification + recommendation |
| `e84fbe1` | UF_FAST_CC default-ON + EUF hot profiler |
| `550132d` | COMB_VALIDATE_SAT (Wisa floor) |
| `a60b3ac` | EMERGENCY STRICT `sawUnderspecified` gate |
| `bfbf16a` | COMB-1 NIA_IFACE_LIFECYCLE default-ON |
| `b4b5ca0` | COMB-2 ARRAY_NOARR_DOWNGRADE default-ON (PARAMOUNT) |

## SMT-COMP submission scope

- All shipped flags are paired-test + reg-validated locally.
- Default-ON flags require no env at SMT-COMP runtime.
- Opt-in flags (COMB_VALIDATE_SAT, DT_VALIDATOR_STRICT, EUF_PROP, etc.) require master CANDFLAGS decision per division.

## Known boundaries

- **QG-classification +363 gap (QF_UF)**: SAT/EUF saturation perf wall, multi-day engineering, not flag-fixable.
- **eq_diamond +81 (QF_UF)**: same perf wall as QG.
- **Bouvier 0/138 (QF_DT)**: cvc5 also TOs at 60s WSL; time-bound, needs master 300s wall.
- **cas / sqrtmodinv (QF_UFNRA)**: NRA-CAC perf lane (NRA agent owns), not EQNA.
- **DT 2600 over-floor on panda14**: deployment / build inconsistency previously diagnosed (binary built without a60b3ac); a60b3ac itself is verified correct.

## Standby triggers (post-Stage 5)

1. Master batch confirms IFACE_LIFECYCLE recovery numbers
2. Master batch confirms ARRAY_NOARR_DOWNGRADE soundness preservation
3. New disagreement surfaces on UF / DT / array combination logics
4. SMT-COMP 2026-06-10 final ship cut-over needs EUF flag promotion review
