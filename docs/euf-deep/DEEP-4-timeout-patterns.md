# DEEP-4 — Timeout patterns per combination division

**Source:** `results/2026-06-01_2359_production_5min_full12/full_5min.sqlite`
**Timeout threshold:** `xolver_allon_time_ms >= 290000` (within 5min wall margin)

## Per-division timeout counts

| division | timeouts | dominant bottleneck |
|---|--:|---|
| QF_UFNIA | **230** | NIA bit-int (Zohar-ic int_check_* family — pow2/intand/intor encodings) |
| QF_AUFNIA | 0 | (all 17 quick-unknown via routing-floor — DEEP-1 A1) |
| QF_UFNRA | 46 | NRA-CAC (cas / sqrtmodinv — heavy real arith) |
| QF_UFLIA | 0 | (small batch sample; Wisa cluster solves or floors quickly) |
| QF_AUFLIA | 0 | (not in batch sample) |

## Bottleneck classification

### QF_UFNIA — NIA bit-int engine wall
Sample: `int_check_bvuge_bvshl0_rtl.smt2`, `int_check_bvugt_bvshl0_rtl.smt2`
- Local 30s: timeout
- Master 5min: timeout
- These cases use UF `pow2 : Int -> Int` + integer-encoded bit ops. NIA modular
  reasoner handles modInv-style but not these general patterns. Track-4
  bit-blast routing partly addresses but doesn't generalize to this shape.
- **Owner: NIA agent (bit-blast extension or new pattern).**

### QF_UFNRA — NRA CAC engine wall
46 timeouts. From prior analysis (cas + sqrtmodinv clusters), both xolver AND
z3 timeout at WSL 30s; z3 wins at master 30-300s via mature CAC tuning.
- **Owner: NRA agent (CAC perf).**

## Sprint actionable observations

- EUF-side bottlenecks NOT observed in timeout sample (E2/E3 FAST_CC already
  default-ON, saturation throughput already addressed).
- Combination-layer bottlenecks NOT observed (Wisa-class hit floor/CMS in
  <1s, not 5min timeouts).
- The 230+46 = 276 timeouts are all theory-engine-limited (NIA / NRA),
  belonging to those agents' lanes.

## Conclusion

No EQNA-lane optimization for these timeout buckets. Routing to NIA/NRA
agents per existing convention. EQNA-lane flags (UF_FAST_CC, IFACE_LIFECYCLE,
COMB_VALIDATE_SAT) are NOT the bottleneck for the timeout class.
