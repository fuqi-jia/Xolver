# Stage 5 — NRA lane summary (2026-06-01 cut-over)

Permanent record of the NRA-lane work delivered on `agent/nra-2` between the
post-integration sync (`3199f1a`) and the Stage 5 cut-over. Every commit ships
default-built but env-flag-gated where appropriate; soundness gate **0 unsound
across all reported sweeps** (143/143 NRA reg + 240-case broad sample + cross-lane
NIA 113/113 + unit 1083/1083 post-J).

This document is the catalog input for `tools/run_differential.sh` CANDFLAGS
promotion and for the Stage 5 ship cut-over decision.

---

## Lever table (13 commits, post-merge)

| Commit | Lever / Subsystem | Mechanism | Acceptance gate | Data point |
|---|---|---|---|---|
| `547ea11` | **S1** LibPolyKernel hash-cons | `binOpCache_` keyed `(op<<60)\|(a<<30)\|b`; canonicalize `(min,max)` for add/mul; NullPoly guarded at call sites. Always-built. | `nra` reg 143/143; binOp hit rate ≥ 50% on standard suite | binOp hit rate **>50%** typical; cache size **bounded by unique inputs** |
| `10e9b55` | S1 stats | `XOLVER_NRA_KERNEL_STATS=1` → destructor prints binOp counters | non-functional | env-gated, default-off |
| `afeda00` | **S1b** cousin hash-cons | `gcd`/`leadingCoefficient` share `binOpCache_` at op codes 5/6; `squareFreeFactors` gets vector-valued `sqfFactorsCache_` | unit + reg | always-on, transitive win |
| `d6a33d3` | S3 preemptive instrumentation | `XOLVER_NRA_CAC_INSTR=1` adds `CacInstr` counters at projection step boundaries; **diagnose only** | non-functional | empirically confirmed `step0_toPrim == step1_toPrim` per cell |
| `2d4e57c` | **LS-C** boundary-score cache | NraLocalSearch `rpCache_` (PolyId→RP) + `termsCache_` (PolyId→MonomialTerm vector) memoize `evalAt`/`scaleAt` | LS unit; NRA reg 143/143 | per-instance cache, valid for kernel lifetime |
| `0acc9f4` | Bonus hycomp/sqrt/Pine sample | 30-case under all levers, documents floor | report-only | 9/10 sqrt, 6/10 hycomp, 5/10 Pine unknown-match |
| `155d407` | **S2** RP-fingerprint memoization | Driver-level cache at `toPrimitiveInteger` entry; key = `RationalPolynomial` FlatMonomialMap fingerprint; pImpl `TpiCacheImpl` to keep RP forward-declared | binOp+tpi hit rate dump | **96.97% hit on nra_022**; pool 660→317 (52%) nra_054; 103→7 (93%) nra_140 |
| `9d6d009` | Task D LS budget derisk | 14-case sweep b=10/25/50/100ms: identical wall, 0 regress | NRA reg + sample | supports default-flip from 10 → 50 |
| `e9c323e` | **Task G** flip `LS_BUDGET_MS` default 10 → 50 | source default in `NraLocalSearch.h`; `XOLVER_NRA_LS_BUDGET_MS` env override preserved | unit 883/883 | empirical: LS converges well within 50 ms on engaging cases |
| `dcac5ed` | **Task H** subResultant audit | PSC cache exists at `XOLVER_NRA_CAC_SR_CACHE`, **default-OFF**, fully implemented sound; recommend adding to CANDFLAGS | code audit | dormant lever, no rebuild needed |
| `9d45652` | **LS-D / Task F** atom-violation cache | NraLocalSearch `violationCache_` keyed `(PolyId, Relation, sub-asg restricted to atom vars)`; `atomVarsCache_` per-poly; FNV-1a hash over mpz limbs | NRA reg 143/143; unit | **98.27% hit on nra_022**; evalAt calls 3354 → 58 |
| `fb8bddb` | **Task E** NLA cluster sweep | 240-case sample × 8 NLA clusters under all levers | broad-corpus sample, 0 wrong | **7/8 ≥ 30% threshold** (see catalog below) |
| `e09e160` | Task E doc fix-up | folded final 3 hycomp cases | non-functional | n=237 → n=240 final |
| `4950213` | **S1c / Task J** `terms()` decomposition cache | `termsCache_` per PolyId (`mutable unordered_map<PolyId, optional<vector<MonomialTerm>>>`); stores nullopt failures; transitive win for `degree()` + `getIntegerCoefficients()` non-main-var paths. Always-built. | unit 1083/1083 (side build); NRA reg 143/143 | hit rate **97.30% / 87.46% / 95.65%** on nra_022 / nra_054 / nra_140; **97.56%** on Melquiond2 (3581-poly stress) |
| `9c2338a` | **S1d / Task J bonus** `variables()` cache | `varsCache_` per PolyId; 92 call sites, structural sharing pattern. Always-built. | unit + NRA reg 143/143 | **96.84%** hit, only 12 distinct sets across 3581 polys |
| `cac4be7` | Task N cross-lane pattern doc | `docs/CAMPAIGN-RULES-hash-cons-audit.md` — methodology for other agents | non-functional | 250-line doc, 4-step audit + 30-line cache template |
| `d993531` | **S1e / Task M** `degree(p, v)` cache | `degreeCache_` keyed `(PolyId<<32)|VarId`. 55 call sites. `intCoeffs` reverted (cold). Always-built. | unit 1083/1083; NRA reg 143/143 | **98.37%** hit, only 6 entries on stress |
| `134a5b0` | **Task I** 1200-case 4-arm NLA sweep | EQNA-trigger broad validation. hycomp+polypaver+Pine × 100 × 4 arms. | broad-corpus, 0 wrong | **polypaver +9 pp LS attribution = master-decision data** |

---

## Task A → J summary

* **Task A — cousin audit** (S1b shipped, `afeda00`): `gcd`/`leadingCoefficient`/
  `squareFreeFactors` cached at kernel layer. `pseudoRemainder` deliberately
  excluded — depends on `main_variable` which `pscChain` mutates, so caching
  would bind to whichever order is installed first.
* **Task B — S3 preemptive** (`d6a33d3`): empirical confirmation that
  `step0_toPrim == step1_toPrim` per cell — justified pursuing S2 driver-level
  memoization independent of any server signal.
* **Task C — bonus 30-case sample** (`0acc9f4`): floor reading on hycomp/sqrt/Pine
  under combined levers; informed Task E scaling.
* **Task D — LS budget derisk** (`9d6d009`): 4-point sweep b=10/25/50/100, 0
  regress. Greenlit Task G default flip.
* **Task E — 240-case NLA sweep** (`fb8bddb`+`e09e160`): see catalog below.
* **Task F — LS-D atom-violation cache** (`9d45652`): 98% hit, single-digit
  evalAt count on dense cases.
* **Task G — LS_BUDGET_MS default 10 → 50** (`e9c323e`): source-baked.
* **Task H — subResultant audit** (`dcac5ed`): PSC cache dormant → CANDFLAGS
  candidate.
* **Task I — EQNA-trigger 100-case 4-arm NLA sweep** (in progress, background
  task `bmx01bz8q`): hycomp/polypaver/Pine × 100 cases × {arm_off, arm_cac,
  arm_lscd, arm_all} under WSL-safe protocol. Validates Task E 30 %
  boundary at statistical scale post-EQNA-P0-close. Report follows.
* **Task J — terms cache** (S1c shipped, `4950213`): see lever table above.
  Found `variables()` and `degree()` as next-tier candidates but neither has
  the same transitive-win surface; deferred unless Task K profiling surfaces
  a specific bottleneck.

---

## Boundary-push catalog (Task E)

7 of 8 NLA clusters cross the master 30 % recovery threshold in the n=30 sample
under the combined lever stack (`LOCALSEARCH=1`, `LS_BUDGET_MS=50`,
`CAC_DEADLINE_MS=2000`, `CAC_SR_CACHE=1`). **0 wrong across 240 cases.**

| # | Cluster | Recovery | Status |
|---|---|---|---|
| 1 | meti-tarski-sin | 100.0 % | perfect — prioritize server batch confirm |
| 2 | meti-tarski-Chua | 96.7 % | 1 timeout |
| 3 | meti-tarski-CMOS | 93.3 % | vindicates sprint 5 bracket-midpoint |
| 4 | meti-tarski-exp | 80.0 % | 6 timeouts → server with full budget |
| 5 | meti-tarski-sqrt | 73.3 % | extends 9/10 Task C signal at scale |
| 6 | meti-tarski-atan | 70.0 % | +673 ATTACK target; 9 cell-jump-bound TO |
| 7 | hycomp | 56.7 % | UNSAT subset reachable; BMC-SAT defers R&D |
| 8 | Pine | 23.3 % | below threshold; defer (architectural) |

**Catalog inclusion**: items 1-7 enter the server batch promotion candidate
list. **Pine** boundary-confirmed, defer to post-SMT-COMP NLA R&D
(architectural ceiling, not engineering surface).

---

## Cross-lane secondary

* **NIA reg 113/113 OFF + ON across the session.** S1+S1b+S2 are
  shared `LibPolyKernel` infrastructure used by `NraSolver` AND any other
  consumer of the kernel; the NIA `LibPolyKernel`-backed paths inherit the
  hash-cons wins transparently. No NIA regressions surfaced.
* **libpoly memory pressure**: peak resident at ~1.7 GB per xolver process
  on hycomp/Pine corpus runs, well under the 4 GB `ulimit -v` cap mandated by
  the WSL-safe protocol. S2 pool collapse (52 % on nra_054, 93 % on nra_140)
  reduces RP allocation churn directly observable as a lower steady-state
  resident footprint.
* **WSL-safe protocol kept throughout**: every sweep used
  `( ulimit -v 4000000; xargs -P 2 ... timeout N ... )`, `cmake --build . -j 2`,
  sample ≤ 30/cluster locally, broader sweeps go server-side.

---

## CANDFLAGS recommended for promotion

For `tools/run_differential.sh` server-batch validation in the upcoming
Stage 5 cut-over:

```bash
XOLVER_NRA_LOCALSEARCH=1
XOLVER_NRA_LS_BUDGET_MS=50      # source default-baked by e9c323e
XOLVER_NRA_CAC_DEADLINE_MS=2000
XOLVER_NRA_CAC_SR_CACHE=1       # Task H derisked, add to differential
XOLVER_NRA_SUBTROPICAL=1        # prior-shipped (1656497, NRA SAT-fast-path)
```

S1+S1b+S2 hash-cons levers are **built-in** (not env-gated) and applied
unconditionally on every NRA invocation; no flag promotion needed.

---

## Decisions resolved by Task I (1200-case 4-arm sweep, `134a5b0`)

1. **`XOLVER_NRA_LOCALSEARCH` default-ON** — **GREEN-LIT**. Polypaver
   `arm_off` 87.0 % → `arm_lscd` **96.0 %** (+9 percentage points, +9
   cases recovered). CAC tuning lever alone delivers +1 pp; LS delivers
   the rest. Hycomp UNSAT-bound 4 arms identical 57.0 %, Pine 0/100
   (architectural). 0 wrong across 1200 runs.
2. **`XOLVER_NRA_CAC_SR_CACHE` default-ON** — derisked sound by Task H,
   confirmed 0-unsound across 1200 runs in Task I.
3. **`XOLVER_NRA_LS_BUDGET_MS=50`** — source default already flipped in
   `e9c323e`, confirmed via Task I (no regression vs arm_off).

---

## Don't-rewrite list (handoff-ready)

These items were investigated and **deliberately not shipped**, with the reason
captured here so a future session doesn't re-attempt them:

* **`pseudoRemainder` hash-cons** — libpoly's `prem` depends on
  `main_variable`, which `pscChain` mutates. Caching by `(p, divisor)` alone
  would bind to whichever variable order is installed at first call → wrong
  result on later calls with different order. Excluded from S1b.
* **Set-cover reason minimisation (NRA brief #1)** — structural no-op at the
  L1 contract level; real version needs `CdcacCore` surgery.
* **`hycomp` SAT-direction broad push** — 912 cases architectural BMC bound;
  Task E confirms 56.7 % UNSAT subset reachable, SAT subset is post-SMT-COMP
  R&D (item #75).
* **`Pine` engineering recovery** — 23.3 % cap is structural; all 7 OKs are
  unknown-match-unknown (Pine declares `:status unknown`). Master spec
  deferred earlier; Task E confirms.

---

## Stage 5 acceptance

* `agent/nra-2` synced with `integration` (`3199f1a`); tip `e09e160` (+13 commits).
* NRA reg **143/143** OFF + ON across the session.
* Unit suite **882/882** (S1) → **883/883** (LS-D add) → carries through.
* Broad-corpus 240-case sample **0 wrong** under combined-lever config.
* WSL-safe protocol observed every step.
* All shipped levers honour invariant 1 (SAT validator-gated) and invariant 7
  (NIA-side, transitive: NRA-style soundness; no NIA UNSAT from incomplete
  reasoning).

Tip: `e09e160` on `agent/nra-2`. Pushed to `origin`.

---

*Author: NRA-lane agent.*
*Date: 2026-06-01.*
*Branch: `agent/nra-2`.*
*Worktree: `/mnt/d/D_Study/BUAA/projects/zolver-nra` (sibling to `NLColver/`).*
