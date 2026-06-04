# NIA Bit-Blast / Bounded-Model Gap vs BLAN — Overnight Diagnosis Log

**Branch:** integration (NIA work to be staged off `agent/nia-2` once code edits start)
**Corpus:** `targeted_nia/` — 87 cases, 18 categories, 3 SAT + 3 UNSAT per category that oracle solves and xolver was failing as of capture.
**Co-oracle:** BLAN at `/mnt/d/D_Study/BUAA/projects/BLAN` (bit-blast truth).
**Goal:** Close BLAN gap (random-sample truth on QF_NIA: xolver 24 vs BLAN 89 / 210; leipzig 0/30).

## Hypothesis on entry (will be refined per iteration)

> xolver's `nia.bit-blast` / BoundedNiaSolver is uncompetitive because vars are unbounded-above so it never picks a width; BLAN wins by searching bit-widths k=1,2,3…

## Architectural facts established (iteration 1)

These are **read-only structural** observations from source — *not* runtime claims.

1. **xolver already has a width-search cascade** for unbounded vars (`BitBlastSolver::solve`, `src/theory/arith/bit_blast/BitBlastSolver.cpp:298-334`):
   - `boxIsComplete=false` (≥1 unbounded var) → cvc5-style cascade: per-var width
     `K = 2 → 4 → 8 → … → maxBW_=128`. Bounded vars keep their exact width.
   - `boxIsComplete=true` → estimator widths + ×4 grow, up to `maxIters_=6` rounds.
   - Verdict-cached on a fingerprint of (poly+rel, per-var [lb..ub]).
   The original hypothesis ("xolver doesn't pick a width") is **falsified at the source level**.

2. **`stageBitBlastEarly` (Standard-effort) has a hard gate**
   (`NiaSolver.cpp:1415-1463`):
   - `XOLVER_NIA_BB_EARLY` env (default-OFF).
   - `normalized_.size() >= XOLVER_NIA_BB_EARLY_MIN_ACTIVE` (default 50).
   - Leipzig has ~20 normalized constraints → **never reaches early bit-blast** under defaults even with the env flag flipped.

3. **`stageBitBlast` (Full-effort)** runs unconditionally; reachability depends on whether the SAT layer ever requests a Full check, and whether prior Full-effort stages decide first
   (order: presolve(F) → nla-cuts(F) → univariate(F) → modular(F) → **bit-blast(F)** → cdcac(F) → local-search(F) → lbbb(F)).

4. **No per-stage trace exists for NIA at runtime today**. NRA has `XOLVER_NRA_STAGE_TIMING` (commit a9bc4e9). NIA only has the shared `ARITH_STAGE_PROF=1`/`ARITH_STAGE_DIAG=1` in `ArithSolverBase::runReasonerPipeline` (`ArithSolverBase.cpp:33-86`), which dumps periodically every 2 s while *between* stages — it cannot pinpoint a single-stage hang.

## Iteration 1 runtime observations (current binary, default profile)

Binary: `build/bin/xolver`, mtime `2026-06-04 23:34:25`.
WSL-safe: `ulimit -v 3 GB`, `timeout 15/30 s`, single process.

### A. Canonical target: `targeted_nia/QF_NIA/leipzig/term-0Hb4yp.smt2`

```
RC=124 (timeout @ 30 s)
stdout: <empty> (no verdict line)
stderr w/ ARITH_STAGE_PROF=1 ARITH_STAGE_DIAG=1 NIA_BITBLAST_DIAG=1: <empty>
```

**Pinned facts:**
- Parser succeeds (`solve <file> --parse-only` → `parse-ok` < 1 s).
- `ARITH_STAGE_PROF` periodic dump (`>=2 s since lastDump`) **never fires** → either (a) NiaSolver `check()` is never reached in 30 s, or (b) a single stage runs ≥30 s without yielding.
- `NIA_BITBLAST_DIAG` **never fires** → `BitBlastSolver::solve` is not entered.

**Implication:** the leipzig timeout is upstream of the bit-blast width loop. The first hypothesis ("xolver doesn't search widths") is the wrong question for this case.

### B. Spot-checked corpus cases (oracle SAT, manifest claims xolver failed)

| case | verdict | wall | comment |
|---|---|---|---|
| `targeted_nia/QF_NIA/AProVE/aproveSMT1006593265001882878.smt2` | **sat** (RC=0) | <2 s | now passes — corpus entry stale |
| `targeted_nia/QF_NIA/calypto/problem-005895.cvc.1.smt2` | **sat** (RC=0) | <2 s | now passes — corpus entry stale |
| `targeted_nia/QF_NIA/leipzig/term-0Hb4yp.smt2` | timeout (RC=124) | 30 s | live target |

A **mass reverify** of all 87 cases at 15 s timeout is running in background
(`/tmp/reverify1.tsv`); the live set is what's left after dropping now-passing
entries. Likely several categories are partially or fully closed already.

## What `boxIsComplete=false` actually does for leipzig

`SpaceEstimator::estimate` sets `boxIsComplete = (every var has hasLower && hasUpper) && !vars.empty()` (`SpaceEstimator.cpp:144`). Leipzig has 38 vars with only `>=0` lower bounds → `boxIsComplete=false`. Per `BitBlastSolver::solve:311-333`:

```c++
unsigned K = 2;
while (true) {
    BitWidthPlan plan;
    for (each var in full.width)
        plan.width[var] = bounded.count(var) ? exact : std::min(K, maxBW_);
    Attempt a = attemptAtWidths(plan, cs, domains, validator);
    if (Sat) return Sat;
    if (Overflow) break;          // larger K only worse
    if (K >= maxBW_) break;       // reached ceiling
    K = std::min(K * 2, maxBW_);  // K: 2,4,8,16,32,64,128
}
return Unknown;                   // box incomplete → never UnsatComplete
```

This *would* be the right algorithm. Today it never runs because Full bit-blast is never reached for leipzig.

## CLI gotcha worth knowing for every diag iteration

`tools/cli/main.cpp:161-163` **silences `std::cerr` by default** (redirects to NullStreambuf). Pass `--verbose` to see *any* stderr output: `[PHASE]`, `[STAGE-ENTER]`, `[STAGE-PROF]`, `[BB-DIAG]`, `[BB-PROF]`. Without it every diag-env knob is invisible. This is the single biggest time-sink to remember.

## Pinned root cause for leipzig (iteration 1 conclusion)

Running with `SOLVE_PHASE_PROF=1 ARITH_STAGE_ENTER=1 NIA_BITBLAST_DIAG=1 --verbose`:

```
[PHASE] enter +0ms (asserts=49)
[PHASE] preprocess-done +5ms (asserts=39)
[PHASE] detect-done +0ms / setup-done +9ms / atomize-done +6ms
... 5 Standard-effort pipeline calls ...
1 Full-effort pipeline call: every stage from pending(F) through bit-blast(F) entered.
After bit-blast(F) entry: no more stages, no [BB-DIAG] verdict line → hang INSIDE BitBlastSolver::solve.
```

Capping bit-width (`XOLVER_NIA_BITBLAST_MAX_BITWIDTH`) and using `NOPRE=1 CONFLICTS=20000`/`50000` confirms the **exact** burn point:

| K_cap | attempts | last verdict | vars at last K |
|---|---|---|---|
| 4 | K∈{2,4} | UNSAT | 4 857 |
| 8 | K∈{2,4,8} | UNSAT | 16 036 |
| 16 | K∈{2,4,8,16} | (hang in K=16 SAT solve) | 56 517 |
| 32 + conflict-budget 20 k | K∈{2,4,8,16} | **SAT-solver-UNKNOWN @ K=16, 56 517 vars** | — |
| 64 + conflict-budget 50 k, 30 s | K∈{2,4,8,16} | **SAT-solver-UNKNOWN @ K=16, 56 517 vars** | — |

**Structural conclusions:**
- The width-search cascade IS running and IS correct (UNSAT at small K is *correct* for leipzig — the 31 intermediate vars n8..n47 receive products that don't fit in 2/4/8 bits even when leaves do; the constraint `n_i = n_a * n_b` forces n_i = n_a·n_b under the K-bit allocation, eliminating most assignments).
- The hang is a single **CaDiCaL SAT solve at K=16** with ~56 k Tseitin vars from 20 product equations × (16·16=256 partial products) + 38 var bits + Tseitin glue.
- BLAN closes leipzig because (a) BLAN-style `varmin` partial-product layout (`BitBlastEncoder.cpp:204` calls out the convention but the call site needs audit), (b) per-cluster CaDiCaL tuning in `BLAN/qfnia/decider.cpp` (`start_bit ∈ {6,5,4,2}`, `re_factor ∈ {4,3,2,1}`, `rephase_factor ∈ {4,4,3,2}` keyed off mul-count thresholds 256/512/1024), (c) BLAN's `preprocessor.simplify()` may shrink leipzig before the bit-blast.

## Already-existing knobs for this lever

(`BitBlastSolver.h` constructor)

| env | default | meaning |
|---|---|---|
| `XOLVER_NIA_BITBLAST_MAX_BITWIDTH` | 128 | cap on per-var width |
| `XOLVER_NIA_BITBLAST_MAX_ITERS` | 6 | cap on outer iters (used by `boxIsComplete=true` path) |
| `XOLVER_NIA_BITBLAST_GATE_BUDGET` | 2 000 000 | encoding var cap (sound — Unknown on overflow) |
| `XOLVER_NIA_BITBLAST_NOPRE` | OFF | disable CaDiCaL elim/subsume/vivify/probe/ternary/transred/decompose |
| `XOLVER_NIA_BITBLAST_CONFLICTS` | 0 (unlimited) | cap CaDiCaL conflicts per internal solve |
| `XOLVER_NIA_BB_EARLY` | OFF | enable Standard-effort bit-blast |
| `XOLVER_NIA_BB_EARLY_MIN_ACTIVE` | 50 | min normalized constraints to fire BB_EARLY |
| `XOLVER_NIA_NO_BITBLAST` | OFF | disable bit-blast entirely (diag A/B) |

## Next steps (queued for iteration 2+)

1. **[infra-committable]** `ARITH_STAGE_ENTER=1` stage-entry trace is now in `ArithSolverBase::runReasonerPipeline` (default-OFF, mirrors `ARITH_STAGE_PROF` idiom). Ready to commit as a diag commit on `agent/nia-bb-3` (off `agent/nia-2`).
2. **[BLAN-run]** Run `BLAN` on leipzig and the rest of the corpus' SAT-polarity entries. For each, record verdict + wall-clock. Build the **`BLAN-fails AND oracle-solves`** subset (per user's instruction) — those need CAC/CDCAC/local-search, not bit-blast.
3. **[encoding audit]** Compare xolver's `PolyBitBlaster::encodePoly` partial-product layout vs BLAN's `BLAN/solvers/blaster/blaster_transformer.cpp`. Specifically: does xolver fold constant coefficients before allocating partial-product bits? Does it CSE shared sub-products across monomials in the same constraint?
4. **[width-skip heuristic]** When a chain of product equations exists (leipzig pattern), the cascade's K=2/4 attempts are nearly-guaranteed UNSAT. Compute a **minimum K floor** from constraint structure (e.g. K0 = ceil(log2(deg+1)) per the longest product chain) and start the cascade at K0 instead of K=2. Diag — no fix yet.
5. **[corpus]** Re-run reverify v3 on the *clean* binary (no concurrent rebuild) — previous run had 67 RC=126 ("Text file busy") races. Tabulate live vs now-passing per category; pick smallest live category for iteration 3's per-category root-cause work.
6. **DEBUG profile** definition: build `tools/run_debug_profile.sh` that sets `XOLVER_NIA_BB_EARLY=1 XOLVER_NIA_BB_EARLY_MIN_ACTIVE=10 XOLVER_NIA_BITBLAST_NOPRE=1` etc., turns OFF soundness floors (so a wrong model surfaces as `(model-mismatch)` from `--check-model`), and re-runs the corpus with BLAN+z3 oracle diff. Profile is for **diagnosis only**; shipped fixes must pass with floors restored, 0-unsound (A3).
7. **[UNSAT cluster]** (per user) For UNSAT-polarity targeted_nia entries that oracle solves but xolver fails: bit-blast isn't usually the right lever. Audit `nia.modular`, `nia.gcd`, `nia.algebraic`, `nia.presolve` per category.
8. **[SAT-non-bitblast cluster]** (per user) For SAT-polarity entries that oracle solves but BLAN can't: route through `nia.local-search` and `nia.cdcac` Full stages, NOT bit-blast. Pre-flag the bit-blast-cascade Unknown-cap return for these so the rest of the pipeline gets a turn.

## Per-iteration commit-gate reminder

A fix commits only when:
- (a) it solves ≥2 NEW held-out cases in its category,
- (b) 0 regressions on full unit + reg buckets + a 200-case random QF_NIA sample,
- (c) 0-unsound with floors restored,
- (d) no magic constants in the diff (default-OFF flag).

Otherwise: keep diagnosing. A no-code iteration that pins a layer is a success.

---

## Per-category root-cause log (appended per iteration)

### category: (TBD after reverify)

(will be filled after iter 2 once `/tmp/reverify1.tsv` is consumed)
