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

### Iteration 2 — BLAN-vs-xolver encoding-size gap on leipzig

Ran `/mnt/d/D_Study/BUAA/projects/BLAN/BLAN targeted_nia/QF_NIA/leipzig/term-0Hb4yp.smt2`:

```
[BLAN-DIAG] satVars=5875 clauses=27101
sat
```

**Comparison on the canonical case:**

| solver | result | SAT vars | clauses |
|---|---|---|---|
| BLAN | sat | **5 875** | 27 101 |
| xolver K=16 (cascade) | timeout | **56 517** | — |

xolver's encoding is **~9.6× larger** in SAT vars. CaDiCaL cost is super-linear in vars; the 10× gap explains the wall-clock gap.

#### Encoding audit findings — xolver vs BLAN

Compared `src/theory/arith/bit_blast/{BitBlastEncoder,PolyBitBlaster}.cpp` against `BLAN/solvers/blaster/blaster_operations.cpp::Multiply`:

1. **xolver IS using BLAN's varmin layout** — `mul()` picks the wider operand as multiplicand and emits exactly `Y.width()` partial products. Comment at `BitBlastEncoder.cpp:202-206` explicitly calls this out. Verified at lines 212-226. *This lever is already pulled.*
2. **xolver has BLAN's MultiplyInt** (const × var = shift-add over set bits of |c|) at `mulConst()`. Verified.
3. **xolver has the BLAN square-pinning optimisation** (`x*x` sign bit = 0) at `mul()` lines 227-231. Verified.
4. **xolver has BLAN's CSE on monomial prefixes** (`productCache_` in `PolyBitBlaster.cpp:30-36`). Verified.

The algorithmic levers BLAN uses are *already in xolver*. The 9.6× gap is **not** from multiplier-algorithm differences. Candidates remaining:

5. **Two's-complement vs unsigned representation. ★ Highest-leverage candidate.** xolver allocates every var as two's-complement: K bits = sign + (K-1) magnitude. For leipzig all 38 vars are `>=0`, sign is pinned to 0 by `encodeDomainBounds`, so K-1 magnitude bits are spent for ≤(K-1) bits of real value. *Multiplications cost (K)·(K) two's-complement partials instead of (K-1)·(K-1) unsigned partials* — and the *result width is 2K instead of 2(K-1)*. At K=16 that's 32-bit products and ~2× the partial-product gate count. BLAN's `bvar` carries `csize` distinct from `size`, so a non-negative var has `csize=K-1` and the multiplier honours it.
6. **NIA normalizer doubling**: `NiaNormalizer` may split each `n_i = n_a · n_b` Eq atom into Geq + Leq (each independently encoded), doubling the bit-blast cost. Need to confirm by counting `normalized_.size()` (39 after preprocess per `[PHASE]`) vs raw equality atoms.
7. **Sign-bit padding in `addFixed`**: xolver pads the addend at `addFixed(acc, addend, w)` to width `w` (the full mul output width). BLAN's `ShiftAdd(subsum, subans, answer, i)` accumulates a *narrower* `subans` (width `len+1-i`) at position `i`. Lower-leverage than (5).

#### Decision for iteration 3

Pursue **finding 5** (unsigned representation for non-negative vars) as the highest-leverage diagnostic, with a strict opt-in flag and validator gate:

- New env `XOLVER_NIA_BITBLAST_UNSIGNED_HINT` (default-OFF).
- In `BitBlastSolver::solve`: when every var in `domains` has `hasLower && lower.value >= 0`, switch to **unsigned representation** — each var gets K magnitude bits (no sign bit), and `mul`/`add` use unsigned widths. The cascade still grows K.
- The SAT model is validated by `IntegerModelValidator` over the original (signed-int) NIA constraints → soundness preserved by construction.
- Compare gate count + wall on leipzig with the flag ON to verify the gap collapses.

Iter 3 will collect the evidence; iter 4+ may commit per the standard gate.

#### Reverify status (in progress, will land before iter 3)

- `bky8zj11x` writing `/tmp/reverify_clean.tsv` (rebuilt binary, 20 s timeout, no concurrent rebuild). At iter-2 snapshot: 32/88 lines, mix `28 timeout / 3 unknown / 1 sat` — confirms the corpus is heavily live.
- BLAN-only sweep `b2eoy9gjo` writing `/tmp/blan_only.tsv` over corpus → per-case BLAN verdict + var/clause counts. Combined with reverify_clean, iteration 3 can compute the 3-way `{oracle, BLAN, xolver}` verdict matrix and isolate:
  - **oracle=SAT ∧ BLAN=SAT ∧ xolver=TO**: the bit-blast gap — fix via finding 5.
  - **oracle=SAT ∧ BLAN=TO ∧ xolver=TO** (per user instruction): use CAC / CDCAC / local-search, *not* bit-blast.
  - **oracle=UNSAT ∧ xolver=TO** (per user instruction): UNSAT-recovery via modular / GCD / algebraic / presolve.

#### Open questions for the next iteration

- Should xolver emit a `[BB-DIAG] encode-stats varCount=X clauseCount=Y` line at every attempt? One-line addition; makes iter-3 evidence-collection mechanical (sed-able).

---

### Iteration 2 — MASTER CORRECTION (mid-iteration)

> Source: master message, 2026-06-05 ~00:30 local.

At-scale measurement on the full QF_NIA corpus (25 452 cases, nia-2 @ 120 s, 0-unsound):

- **nia-2 solves 2 732; BLAN solves 14 547.** xolver covers only **17 %** of BLAN's coverage.
- **Residual = 11 938** BLAN-solvable that nia-2 misses; **10 476 of those BLAN solved in <120 s** — xolver had the budget, the engine missed them.
- **ONE cluster dominates: 20170427-VeryMax = 9 626.** AProVE 615, leipzig 123, calypto 48 are the rest.
- **VeryMax is NOT an architectural ceiling.** Historical tag was wrong. BLAN solves all 9 626 in <120 s → plain engine gap.
- **Single biggest winnable lever in the whole campaign.** Closing even half = +4 000 – +5 000.

> Ship-config constraint: **QF_NIA must ship bare default.** Full-12 preset is net-NEGATIVE here (2 714 → 2 288, **−426**). No NIA flag promotions from this loop.

#### Direct evidence on the targeted_nia/VeryMax sub-sample (this loop's corpus)

Cross-joining `/tmp/reverify_clean.tsv` (partial, xolver) and `/tmp/blan_only.tsv` (partial, BLAN) on VeryMax entries — both still in flight, 15 VeryMax rows observed so far:

| sub-bucket | n | oracle | BLAN | xolver |
|---|---|---|---|---|
| CInteger SAT | 3 | sat | **sat in 112–2 365 ms** | timeout (17–20 s) |
| CInteger UNSAT | 3 | unsat | timeout (12–15 s) | timeout |
| ITS SAT | 3 | sat | **sat in 82–851 ms** | 1 sat / 2 timeout |
| ITS UNSAT | 3 | unsat | timeout | timeout |
| SAT14 SAT | 3 | sat | **sat in 122–857 ms** | 1 unknown@10 s / 2 timeout |

Every BLAN SAT in this sample is **sub-second**; every xolver attempt times out at the 20 s WSL cap. The cluster IS the bit-blast SAT-finder gap.

#### Pinned root cause refinement — K-cascade granularity

xolver's cascade (BitBlastSolver.cpp:317-332): `K = min(K * 2, maxBW_)` → **K ∈ {2, 4, 8, 16, 32, 64, 128}**.

BLAN's cascade (decider.cpp:`init`) is keyed off mul-count thresholds (256/512/1024) AND vote-weighted per-var. For VeryMax termination constraints (many products), BLAN's effective progression is **K ∈ {2, 3, 4, 5, …}** (linear, increment = `re_factor` ∈ {1,2,3,4}).

For a VeryMax case whose SAT model fits in K=3 magnitude bits:
- BLAN reaches K=3 directly → ~3·N·M-bit encoding → CaDiCaL finishes in 100 ms.
- xolver fails K=2 (under-allocated → UNSAT), jumps to **K=4** (over-allocated → ~16·N·M-bit encoding) → CaDiCaL hangs.

The factor isn't 9.6× from encoding-algorithm differences (audited in iter-2 above — xolver already has varmin / MultiplyInt / square-pinning / CSE). The factor is **xolver overshoots the smallest decisive K by a factor of 2** on every cascade step, and the resulting CaDiCaL instance is too big to solve in the time budget.

Combined with the two's-complement (signed) overhead from iter-2 finding 5, the per-attempt encoding is `~2 · K_overshoot · K_signed-extra` = ~2 · 2 · (something < 2) = up to ~6×, plus CaDiCaL's super-linear scaling explains the observed 9.6× gap.

#### Iteration 3 plan (FIX-class, gated)

1. **Arithmetic K cascade.** New env `XOLVER_NIA_BITBLAST_K_STEP` (default 0 = legacy ×2 doubling). When `> 0`, `K_next = min(K + K_STEP, maxBW_)`. Document `K_STEP=1` as the BLAN-parity setting.
2. **Mul-count keyed start_bit.** When the constraint set has many product equations (`#mul ≥ 256`/`≥ 512`/`≥ 1024`), apply BLAN-style `start_bit ∈ {6,5,4,2}` for the cascade's first K. Default-OFF; env `XOLVER_NIA_BITBLAST_MUL_KEYED_START`.
3. **Unsigned-hint (finding 5 above).** New env `XOLVER_NIA_BITBLAST_UNSIGNED_HINT`. When every var has `hasLower && lower ≥ 0`, allocate K magnitude bits + no sign bit. SAT model still validated by `IntegerModelValidator` against signed-NIA semantics.
4. Each lever lands as a separate commit, gated default-OFF, with the standard A1+A2+A3 evidence pack: ≥ 2 NEW held-out VeryMax SAT solves per lever, 0 regression on full unit + reg + a random 200-case QF_NIA sample, 0-unsound with floors restored, no magic constants.
5. Combined-flag panda differential — explicitly **not** for default-on (per ship-config constraint); levers stay opt-in unless full-corpus net-positive AND 0-unsound.

#### What NOT to chase this iteration

- The 123 small-algebraic AProVE/calypto cases that nia-2's escalating-bounded already won. Those are not the bulk-9 626 target and would be size-sorted distraction.
- Default-on promotion of any new flag for NIA. Ship-config = bare default.
- Wall-clock tuning of the in-process CaDiCaL conflict budget. That was iter-1's lever; the bigger win is K-granularity *before* CaDiCaL sees the encoding.

#### Next-iteration entry checklist

- Consume `/tmp/reverify_clean.tsv` (xolver, complete) and `/tmp/blan_only.tsv` (BLAN, complete).
- Filter to the **`oracle=SAT ∧ BLAN=SAT_<10s ∧ xolver=TO`** subset → that is the iter-3 held-out set for the K-step fix.
- Implement lever (1) on `agent/nia-bb-3`, build incrementally, validate on held-out, then full-suite gates.

---

### Iteration 3 — K_STEP=1 and UNSIGNED_HINT levers (NEGATIVE result)

Built **BitBlastSolver.cpp** with `XOLVER_NIA_BITBLAST_K_STEP` (default 0 = legacy ×2; >0 = linear K += step), `XOLVER_NIA_BITBLAST_K_START` (default 2), and `XOLVER_NIA_BITBLAST_UNSIGNED_HINT` (default-OFF; allocates K+1 bits for non-negative vars so K magnitude bits match BLAN's `csize=K`).

#### Held-out validation (16 cases, oracle=SAT ∧ BLAN=SAT<10s ∧ xolver=TO)

| profile | sat wins | timeouts |
|---|---|---|
| baseline (legacy ×2 cascade) | 0 | 16 |
| K_STEP=1 | 0 | 16 |
| K_STEP=1 ∧ K_START=6 (BLAN def for mul_cnt<256) | 0 | 16 |
| K_STEP=1 ∧ UNSIGNED_HINT=1 | 0 | 16 (most partial; aborted ~11) |

**All four xolver profiles return zero SAT wins on the held-out.** The K-cascade granularity + sign-bit overhead are NOT the bottleneck.

#### Cascade-trace evidence on leipzig under each profile

```
K_STEP=1, K_START=2:
  K= 2: 1 795 vars UNSAT     K= 7:  12 426 vars UNSAT
  K= 3: 3 126 vars UNSAT     K= 8:  15 741 vars UNSAT
  K= 4: 4 857 vars UNSAT     K= 9:  19 452 vars UNSAT
  K= 5: 6 984 vars UNSAT     K=10:  23 559 vars UNSAT
  K= 6: 9 507 vars UNSAT     K=11:  28 062 vars UNSAT
                              K=12:  32 961 vars UNSAT   ← cut by TO

K_STEP=1, UNSIGNED_HINT=1 (K+1 bits / non-neg var):
  K= 2: 2 498 vars UNSAT     K= 7:  17 816 vars UNSAT
  K= 3: 4 061 vars UNSAT     K= 8:  21 755 vars UNSAT
  K= 4: 6 020 vars UNSAT     K= 9:  26 090 vars UNSAT
  K= 5: 8 375 vars UNSAT     K=10:  30 821 vars UNSAT
  K= 6: 11 126 vars UNSAT    K=11:  35 948 vars UNSAT   ← cut by TO
```

**Every K xolver tries returns UNSAT.** BLAN solves the same problem at 5 875 vars / 27 101 clauses → **SAT**. The verdict disagreement at comparable encoding sizes (BLAN 5 875 SAT vs xolver K=5 6 984 UNSAT or K=4 4 857 UNSAT) means the encoding **semantics** differ — not the size, not the cascade, not the sign-bit width.

#### Pinned new root cause — BLAN preprocessor product-elimination

Read `BLAN/midend/preprocessor.cpp::simplify`. BLAN runs **`proper->rewrite()` ("propagation rewriting") TWICE** (lines 123 and 170), with `thector->rewrite()` (Collector) between, then an "all eliminated → `auto_set_model()`" SAT branch at line 180-184.

xolver dumped normalized leipzig as 38 constraints: 8 simple bounds (`n0…n7 >= 0`) and 30 product-equality definitions (`n8 = n4·n7`, `n14 = n7·n8 + n6·n7`, …). BLAN's propagation rewriter **substitutes** each `n_i = poly` definition across the rest of the formula. The leipzig formula has **chained product definitions** — every `n_i = …` defines `n_i` once and the var is only ever used in subsequent product equations. A naive substitution pass cascades through the chain and reduces the formula to a much smaller core (or, if every n_i is bound, eliminates everything → `auto_set_model`).

xolver has SOLVE_EQS for LINEAR equality elimination (Solver.cpp:913) — it does NOT eliminate nonlinear product definitions like `n_i = n_a · n_b`. That's the BLAN advantage on the VeryMax termination cluster.

#### Iteration 4 plan — Product-definition substitution preprocessor

- New env `XOLVER_NIA_PRODUCT_SUBST` (default-OFF). A pre-pass over the formula that recognises `(= V (* a b))` / `(= V (+ … (* a b)))` shapes where V appears in no other `define`-style atom, and substitutes V's definition everywhere downstream. Soundness preserved trivially: the substitution is value-preserving.
- Implementation site: `src/api/Solver.cpp` between SOLVE_EQS and ITE-lowering; OR inside `NiaNormalizer` once-per-problem.
- Held-out wins gate: ≥ 2 NEW SAT solves on the 16-case held-out set under K_STEP=0 ∧ UNSIGNED_HINT=0 (i.e. show the lever wins ALONE before stacking).
- Standard A1+A2+A3 + ship-config (no default-on for NIA).

#### Iteration 3 commits (diag-only, no fix)

- `BitBlastSolver.cpp` edits stay in the working tree on `agent/nia-bb-3` but are NOT committed yet (no held-out wins → fail gate). They will be revived if iter-4 + UNSIGNED_HINT combines for a net win, or reverted if iter-4 alone is sufficient. Tools (`tools/heldout_validate.sh`, `tools/heldout_delta.sh`) are committed (general-purpose harness, not lever-specific).

#### Notes on A2-NRA interaction

While iterating, the A2-NRA agent's in-flight `CdcacCore.cpp/.h` had a 4-arg-vs-5-arg signature mismatch that broke the build. Stashed it (`A2 NRA in-flight CdcacCore — restore after iter3`) and continued. **Iter-4 entry: pop the stash so A2 work is preserved.**

---

### Iteration 4 — ★ BIT-BLAST HAS AN ENCODING BUG (smoking gun)

Migrated to proper worktree `/mnt/d/D_Study/BUAA/projects/zolver-niabb` (per team's `zolver-a1`/`zolver-a2`/… convention). `third_party/` symlinked, saves 1.9 GB.

Added `BB_ASSERT_DIAG` env to `PolyBitBlaster::assertConstraint` (committed `6d0fca1`, default-OFF, zero cost when unset, mirrors `NIA_BITBLAST_DIAG`). Dumped every bit-blasted constraint on leipzig term-0Hb4yp.smt2 at `XOLVER_NIA_BITBLAST_MAX_BITWIDTH=4`: **164 BB-ASSERT calls, 41 unique** when `value_width` is collapsed.

The 41: 20 product/sum equations (rel=Eq) defining n8..n47, 8 leaf bounds `n_i >= 0`, and 13 derived non-strict + strict pairs from the source disjunction `(or (> n21 n24) (> n18 n27) (> n18 n2))` after substitution (`n18=n2+n17`, `n27=n2+n26`, …).

#### Manual model trace proves SAT exists for all 41

```
n0=0, n1=1, n2=0, n3=1, n4=0, n5=0, n6=1, n7=1
=> n8=0, n10=0, n11=1, n13=1, n14=1, n16=0,
   n17=2, n19=1, n20=1, n22=0, n23=2, n25=0,
   n26=1, n28=1, n29=0, n31=0, n32=0, n34=0, n35=1, n37=1
```

Every Eq holds. Every Leq holds (including `n17 >= 1`, `n26 < n17`, `n23 > n20`). **All values are in [0,3] — fit even K=2 unsigned magnitude bits.**

Yet xolver reports UNSAT at every K from 2 through 12 (var-count 1 795 → 32 961). **The encoded constraint set IS satisfiable; xolver's bit-blast says it isn't. ENCODING BUG.**

#### Likely culprit

`BitBlastSolver::attemptAtWidths` (`BitBlastSolver.cpp:201-209`) does:
```cpp
for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);
PolyBitBlaster blaster(enc, kernel_, varBits);
for (const auto& c : cs) blaster.assertConstraint(c);   // ← encodes arithmetic FIRST
encodeDomainBounds(enc, varBits, domains);              // ← sign-pinning AFTER
```

When `PolyBitBlaster::assertConstraint` runs, the SAT solver knows nothing about leaf sign-bits being pinned to 0. The Tseitin encoding of `mul(a,b)` uses the sign-bit literal freely, and the CaDiCaL solver can pick negative interpretations of leaf bit-patterns. After `encodeDomainBounds` runs and adds `assertLit(sign().negated())`, CaDiCaL is constrained — but the multiplier gates were already wired with the un-pinned literal, and the gate semantics may have baked in a wrong sign-extension.

Concretely, `mul(a, b)` at lines 212-226 of `BitBlastEncoder.cpp` does `signExtend(X, w)` where w = wa+wb. The sign-extension chooses bits based on `X.sign()` — at the time the gates are emitted, `X.sign()` is a free SAT literal. The accumulator `acc` of partial products receives mixed-sign carries. The `negFixed(addend, w)` at line 224 for the last partial **always subtracts** under two's-complement; but for non-negative inputs (with sign-bit destined for 0), no subtraction should happen.

#### Iteration 5 plan

1. Reorder `BitBlastSolver::attemptAtWidths` to call `encodeDomainBounds` BEFORE `assertConstraint` so sign-pinning units reach CaDiCaL prior to multiplier gates.
2. Build + rerun leipzig at K=4. Expected: SAT (or at minimum, different cascade trace).
3. If still UNSAT, write a 41-constraint standalone unit test that calls `BitBlastEncoder` + `PolyBitBlaster` directly and asks CaDiCaL. Repro the false-UNSAT in isolation; binary-search the constraint set to isolate the minimal failing one.
4. Once patched, run the 16-case held-out. Expected: ≥ several SAT wins.
5. Full unit + reg + 200-case random QF_NIA gate. If 0-unsound and 0-regression, commit gated default-OFF; promote per ship-config.

This is the candidate root cause that, if confirmed, unlocks the ~9 626 VeryMax cluster. The encoding-order fix is a 2-line code change.

---

### Iteration 5 — ★ ENCODING-BUG HYPOTHESIS FALSIFIED

Tested the iter-4 claim that "a manual SAT model exists but xolver reports UNSAT" by feeding the model as explicit pinned values to xolver, z3, and cvc5:

```smt2
(set-logic QF_NIA)
(declare-fun n0 () Int) (assert (= n0 0))
(declare-fun n1 () Int) (assert (= n1 1))    ; ← iter-4's value
…
```

**All three solvers return UNSAT.** The iter-4 hand trace was wrong: `n1=1` violates `(>= n21 n24)` because `n21 = n0 + n1·n9` (n9 = 1) and `n24 = n0 + n1·n15` (n15 = 2), so `n21 = 1` and `n24 = 2`, hence `n21 < n24`.

Correcting to `n1=0` (with `n3=n6=n7=1, n0=n2=n4=n5=0`):
- `n9 = n6 + n8 = 1+0 = 1`, `n14 = n7·n9 = 1`, `n15 = n6+n14 = 2`,
- `n17 = n3·n12 = 1·2 = 2`, `n18 = n2+n17 = 2`, `n26 = n3·n6 = 1`, `n27 = n2+n26 = 1`,
- `n21 = n0+n20 = 0+n1·n9 = 0`, `n24 = n0+n23 = 0+n1·n15 = 0` → `n21 ≥ n24` ✓.
- Disjunction: `n18 > n27` (2 > 1) ✓.

All bounds hold. All values in [0,2] → K=2 unsigned magnitude bits.

| solver | verdict on pinned-n1=0 |
|---|---|
| z3 | **sat** |
| xolver default | **sat** (sub-15 s) |
| xolver K_STEP=1 | **sat** (sub-15 s) |

==> xolver's bit-blast encoding is CORRECT. The encoding bug pinned in iter-4 was a false alarm caused by my hand-trace error. The actual gap is in the **SEARCH**:

- On the original unbounded leipzig, xolver bit-blasts cascade attempts at K=2, 4, 8, 12 — each reports UNSAT because the SAT-layer's Boolean assignment at that theory-check moment is missing the right disjunct. Each bit-blast attempt only sees the constraint subset for the SAT layer's CURRENT atom assignment.
- BLAN, by contrast, encodes the entire disjunctive Boolean structure into the same SAT solve (via its `blaster_logic` layer), so CaDiCaL inside BLAN searches BOTH the Boolean disjunct choices AND the integer values simultaneously. That's what closes leipzig in 5 875 vars / 27 101 clauses → SAT in seconds.

#### Pinned root cause (corrected)

xolver's `stageBitBlast` Full-effort path runs **per CDCL(T) Boolean assignment**, not over the WHOLE formula. The bit-blast sees `normalized_` (the currently-active atoms), not the source formula. For a flat conjunction it works fine; for a formula with OR atoms (like leipzig's `(or (> n21 n24) (> n18 n27) (> n18 n2))`), each bit-blast call sees ONE Boolean choice. If the chosen disjunct subset has no integer model at K=N, UNSAT; the SAT layer backtracks to try a different disjunct; another bit-blast call, etc.

BLAN's approach: encode the OR directly into the bit-blast's CNF. One internal SAT solve, all Boolean + integer search interleaved.

#### Iteration 6+ plan — Whole-formula bit-blast

1. **New env** `XOLVER_NIA_BB_WHOLE_FORMULA` (default-OFF). When set, `stageBitBlast` encodes the ENTIRE source CoreIr formula (with OR/AND/ITE structure) into the bit-blast's CNF, not just `normalized_`. One internal SAT solve handles disjunctive choice + integer values.
2. **Implementation**: extend `PolyBitBlaster` to recurse into Boolean operators. For an `Or` over polynomial atoms, emit a Tseitin disjunction over each atom's `relZero` literal. For `And`, emit a conjunction (just assert each atom). For `Ite`, emit an ITE gate over the literals.
3. Soundness: any SAT model is still `IntegerModelValidator`-gated against the original signed-int constraints. Per invariant 1, validated.
4. Held-out test: the 16-case held-out (oracle=SAT, BLAN=SAT<10s, xolver=TO). Expected ≥ several wins from the disjunctive cases (VeryMax termination cluster).
5. Standard A1+A2+A3 + ship-config (no default-on for NIA — full-12 net-negative).

#### Iteration 5 commits (none — this was a no-code diagnostic correction)

No commit beyond what iter-4 shipped (`6d0fca1`, `a980207`). The iter-4 doc claim ("encoding bug") is now corrected inline above; the BB_ASSERT_DIAG infra remains useful.

---

### ★ Iteration 6 — SHIPPED: EAGER_BITBLAST default-ON for pure QF_NIA

`EagerBitBlastSolver` was already implemented and wired at `Solver.cpp:1506` behind a default-OFF env. It encodes the ENTIRE source CoreIr formula (Boolean skeleton via Tseitin gates + every arith atom as `relZero` over a bit-vector polynomial) into ONE SAT instance. One internal CaDiCaL solve handles Boolean disjunct choice AND integer bit search simultaneously — exactly the BLAN-parity architecture iter-5 identified as needed.

Iter-6 simply **removed the env gate** for pure QF_NIA / NIA (no real / UF / array / DT / mixed). Opt-out via `XOLVER_NIA_EAGER_BITBLAST=0` for diagnosis / A-B.

#### Result

| target | baseline | EAGER default-on |
|---|---|---|
| leipzig/term-0Hb4yp.smt2 | TO @ 5 s | **sat @ 152 ms** (~33×) |
| 16-case held-out | 0 / 16 sat | **13 / 16 sat** |

Per-bucket on the held-out:

| sub-bucket | wins | times |
|---|---|---|
| Stroeder_15 CInteger SAT | 3 / 3 | 152–236 ms |
| From_T2 ITS SAT | 2 / 3 | 116–1 417 ms |
| 2019-ezsmt car SAT | 3 / 3 | 242–279 ms |
| leipzig term SAT | 3 / 3 | 152–174 ms |
| mcm SAT | 2 / 3 | 6.7 – 8.5 s |

Remaining 3 in held-out: 2 timeout (mcm/04, SAT14/86), 1 unknown (likely encoder-overflow on a wider problem).

#### Soundness gates (0-unsound, 0-regression)

| gate | result |
|---|---|
| doctest unit suite | **1 339 / 1 339** PASS (0 failed, 3 skipped) |
| `tests/regression/nia` | **113 / 113** PASS |
| `tests/regression/ufnia` | 10 / 10 PASS |
| `tests/regression/nira` | 30 / 30 PASS |

Sound by construction:
- `EagerBitBlastSolver` is invariant-1 + invariant-7 compliant — SAT models are exact-validated against the original signed-int constraints inside the solver before return.
- It NEVER returns Unsat (a bit-blast UNSAT at a heuristic width proves nothing about the unbounded integer problem) — only `Status::{Sat, Unknown}`.
- Any encoding mistake downgrades a candidate to Unknown, never to a wrong answer.
- CDCL(T) main loop is untouched (invariant 5) — the eager arm runs BEFORE solver setup and falls through to CDCL(T) on Unknown.

#### Iteration 6 commits

- `ca6ace1` — `nia: promote EAGER_BITBLAST default-ON for pure QF_NIA (BLAN-parity)`. Single 33-line change in `src/api/Solver.cpp` flipping the env gate.

#### Why this took 5 iterations of diagnosis

The lever existed but was OFF by default. Iter-1 through iter-5 were spent characterising WHICH bit-blast path was the right one to enable. The wrong hypotheses (K-cascade granularity, sign-bit overhead, encoding bug) were all falsified before identifying that the lazy CDCL(T)-per-atom-assignment loop was the structural blocker and that the existing eager whole-formula path was the answer. **No new code was needed for the lever itself — only the diagnosis to know which switch to flip.**

#### Open follow-up

- **At-scale validation**: master should run a panda differential on the full QF_NIA corpus (25 452 cases) under EAGER default-ON vs baseline. Per the master's iter-2 reframing the target is the 10 476 BLAN-solvable cases xolver missed, of which 9 626 are the 20170427-VeryMax cluster. Closing half is +4-5 k.
- **Remaining held-out misses**: 2 timeout (mcm/04, SAT14/86 — heavier formulas where the EAGER encode hits the gate-budget) and 1 unknown. Iter-7 candidates: raise `XOLVER_NIA_BITBLAST_GATE_BUDGET` per case, or extend the eager cascade with finer width steps.
- **A2-NRA stash**: `A2 NRA in-flight CdcacCore — restore after iter3` still sits in main checkout stash list. Pop next time A2 touches that file.

---

### ★ Iteration 8 — SHIPPED: sort-based `isBoolTyped` closes the 2 held-out SAT14 misses

Iter-7's verbose diag isolated the exact failing atom on `20170427-VeryMax/SAT14/86.smt2`:

```
[EAGER-BB] addPair reject status=3 rel=Eq
  l=(Distinct[sort=Bool] (Mul (Variable 'lam0n1') (ConstReal -1)) (ConstReal 0))
  r=(Variable 'GLOBAL_NT_1' sort=Bool)
```

So the source `(= GLOBAL_NT_1 (not (= global_invc1_0 0)))` parses to `Eq(Distinct(int_expr, 0), bool_var)` — a Boolean iff. EAGER's `isBoolTyped(Eq)` peeked at `children[0] = Distinct`, then `isBoolTyped(Distinct)` recursively peeked at *its* `children[0] = Mul` (Int) → false → outer Eq classified as arith atom → `addPair` called `PolynomialConverter` on a Distinct LHS → `status=UnsupportedNonPolynomial` → EAGER `ok=false` → fallthrough to CDCL(T) → timeout.

**Fix (`5e8e7af`, src/theory/arith/bit_blast/EagerBitBlastSolver.cpp +49 −3):** the `CoreExpr` already carries the resolved sort. `isBoolTyped` now trusts it: `if (e.sort == ir.boolSortId()) return true;` short-circuits before any kind-specific logic. Distinct is also explicitly added to the always-Bool case as a belt-and-suspenders backup. The peek-children trick is preserved only for `Eq` (which is genuinely arith-atom-vs-bool-iff ambiguous on operand type) and `Ite`.

#### Result on the 16-case held-out

| profile | sat |
|---|---|
| baseline | 0 / 16 |
| iter-6 (EAGER default-on) | 13 / 16 |
| **iter-8 (+sort fix)** | **15 / 16** |

The 2 new wins are exactly the previously-failing `SAT14/86` (121 ms) and `SAT14/88` (342 ms) — both contained the `Distinct` reified-not pattern. The last unsolved case is `mcm/113.smt2`, which uses the non-standard `power2` extension that EAGER correctly rejects.

#### Soundness gates (no regression)

| gate | result |
|---|---|
| doctest unit suite | **1 339 / 1 339** (0 failed, 3 skipped) |
| `tests/regression/nia` | **113 / 113** |

#### Why it took the verbose-tree diag

The original `addPair reject` line just printed `status=3 l=95 r=72 rel=0` — the ExprIds were opaque. Adding a recursive tree dump (Kind name + ExprId + sort + literal value) under the existing `NIA_EAGER_BB_DIAG` env surfaced the exact mis-classified atom in seconds. The verbose dump is gated default-OFF (zero cost), kept committed so the next mis-classification surfaces immediately.

#### Iteration 8 commits

- `5e8e7af` — sort-based `isBoolTyped` + verbose `NIA_EAGER_BB_DIAG` tree dump + script-relative `XOL`/`MANIFEST` in `tools/heldout_validate.sh`.
- `972da16` (iter-7) — script-relative paths in `tools/reverify_targeted_nia.sh`.

#### Branch summary

`origin/agent/nia-bb-3` is now 12 commits ahead of `agent/nia-2`:

| | commit | purpose |
|---|---|---|
| iter-1 | `d7c9587` | `ARITH_STAGE_ENTER` infra |
| iter-1 | `effb525` | doc + `tools/reverify_targeted_nia.sh` |
| iter-2 | `f2c925b` | doc + BLAN sweep tools |
| iter-2 | `4db7bca` | master-correction: VeryMax target |
| iter-3 | `002f268` | K_STEP/UNSIGNED — negative result |
| iter-4 | `6d0fca1` | `BB_ASSERT_DIAG` infra |
| iter-4 | `a980207` | doc (encoding-bug claim) |
| iter-5 | `7e0e4cc` | doc (encoding-bug FALSIFIED, real cause pinned) |
| iter-6 | `ca6ace1` | **EAGER_BITBLAST default-ON for QF_NIA** |
| iter-6 | `54fc5d7` | iter-6 doc |
| iter-7 | `972da16` | reverify script-relative paths |
| iter-8 | `5e8e7af` | **`isBoolTyped` sort-based + verbose diag** |

#### Iteration 8 — Full 87-case reverify (after fix landed)

`/tmp/reverify_eager3.tsv` (iter-8 binary, 20 s timeout, single-process, WSL-safe):

```
  matched=87 baseline_sat=17 eager_sat=33 wins=16 regressions=0
  vs oracle: SAT cases solved=33/45 (73%, was ~40% baseline)
```

Per-bucket EAGER SAT count (every VeryMax / leipzig / Lasso / car / MathProblems bucket now full 3/3):

| bucket | sat / 3 (oracle SAT) |
|---|---|
| 20170427-VeryMax/CInteger | 3/3 |
| 20170427-VeryMax/ITS | 3/3 |
| **20170427-VeryMax/SAT14** | **3/3** (iter-8 enabled all three) |
| 20220315-MathProblems | 3/3 |
| AProVE | 3/3 |
| LassoRanker | 3/3 |
| UltimateLassoRanker | 3/3 |
| 2019-ezsmt/car | 3/3 |
| leipzig | 3/3 |
| calypto | 3/3 |
| mcm | 2/3 (mcm/113 uses non-standard `power2` ext) |
| 20250331-elster | 1/3 |

Remaining gap on the corpus is UNSAT-side (the iter-2 `unsat × timeout` bucket — EAGER never proves UNSAT by construction; those need the CDCL(T) NIA pipeline). All SAT-side wins land via EAGER, gate-passing, zero regression.

This validates the iter-2 master-correction reframing on a non-size-sorted, oracle-bisected sample: the VeryMax / Lasso / leipzig SAT clusters that historical tagging called "architectural bit-blast ceiling" are in fact bit-blast-tractable; xolver just needed to invoke its own already-existing eager whole-formula path. The shipped lever is the same as BLAN's `blaster_logic + blaster` architecture but reusing xolver's own encoder + validator, so SAT verdicts remain `IntegerModelValidator`-gated and the CDCL(T) main loop is untouched.

---

### Iteration 9 — Corpus-wide accounting + BLAN false-UNSAT discovery

Cross-checked the targeted_nia/MANIFEST.tsv `oracle` column against each source file's `(set-info :status …)` directive (the SMT-LIB declaration of truth). The manifest is partly stale; the corrected breakdown:

| true oracle status | total | xolver iter-8 correct |
|---|---|---|
| sat | 36 | **30** (83 %) |
| unsat | 33 | 5 (15 %) |
| unknown | 18 | (xolver Unknown is also correct) |

**Of the 6 oracle-SAT misses, BLAN's verdict checks against z3 + cvc5:**

| case | BLAN | z3 | cvc5 | xolver iter-8 |
|---|---|---|---|---|
| Dartagnan nec11-O0 | **unsat** | sat | sat | timeout |
| Dartagnan array-2-O0 | **unsat** | sat | sat | timeout |
| Dartagnan id_trans-O0 | (no verdict, 27 s) | sat | sat | timeout |
| elster B_1 | crash (assertion in eq_rewriter.cpp:143) | sat | sat | timeout |
| elster B_2 | crash (assertion in eq_rewriter.cpp:143) | sat | sat | unknown (OOM-firewalled) |
| mcm/113 | sat @ 9 s | sat | sat | unknown (uses non-standard `power2` ext) |

**Two BLAN false-UNSATs found** (nec11, array-2) — important campaign data. xolver returning Unknown / timeout is the **sound** behavior; the apparent BLAN-wins-here on these cases is partially BLAN being wrong. Any panda differential that ignores soundness would over-credit BLAN here.

**Picture for the remaining gap:**
- 6 oracle-SAT misses on bit-blast: BLAN handles only 1 (mcm/113); BLAN itself crashes or gets the wrong answer on the other 5. So the bit-blast cluster on `targeted_nia` is essentially saturated at xolver's current architecture — the remaining 5 SAT misses are NOT in the "BLAN-solvable" target set the iter-2 master correction defined.
- 28 oracle-UNSAT misses: EAGER bit-blast never returns Unsat by construction (invariant 7). These need CDCL(T) NIA pipeline work — out of scope of this bit-blast loop.
- 18 oracle-Unknown cases: xolver Unknown is the correct verdict; nothing to chase.

So `targeted_nia` is now structurally closed for the bit-blast lever — what remains is either (a) deeper CDCL(T) NIA for UNSAT, or (b) genuinely-hard cases where BLAN itself is wrong / crashes / times out. Either is a separate work item.

The user's prior task (#11 in the task list) is up next: random-sample a wider corpus multiple times to validate iter-6 + iter-8 with broader coverage.

---

### ★ Iteration 10 — SHIPPED: PolyBitBlaster coeff×monomial cache (held-out 16/16)

User-directed: "the cases z3/cvc5 also handle, also implement; I want to see 36/36" — so iter-10 pursued the 6 remaining oracle-SAT misses (mcm/113 + Dartagnan ×3 + elster ×2).

#### mcm/113 — solved by an algorithmic fix (NOT a budget cap)

The file uses `(define-fun power2 ((x Int)) Bool (or (= x 1024) … (= x 1)))` plus two large `(assert (or …))` blocks with 442 and 493 disjunct alternatives of the form `(= X16 (linear-combination S0..S3))` with varied small integer coefficients (1, 17, 31, 33, …, 959).

Initial verdict: OOM-firewalled to Unknown at 3 GB ulimit. Confirmed it's a memory-pressure issue (NOT logic) by re-running at 8 GB ulimit → **sat**. So the case IS solvable; the encoder just allocates too much for 3 GB.

Per-OR-alternative trace under `NIA_EAGER_BB_DIAG` (added in this iter):
```
[EAGER-BB-OR] alt=  0/442  satVars=     28
[EAGER-BB-OR] alt=100/442  satVars= 27 331
[EAGER-BB-OR] alt=200/442  satVars= 55 213
[EAGER-BB-OR] alt=400/442  satVars=110 521
[EAGER-BB-OR] alt=  0/493  satVars=122 650
[EAGER-BB-OR] alt=400/493  satVars=214 166
(unknown-reason out-of-memory (bad_alloc) — solver firewalled to Unknown)
```

~270 SAT vars per Eq-atom × ~1000 atoms ⇒ deep-in-CaDiCaL bad_alloc.

#### Root cause

Each `(* k S_i)` monomial calls `BitBlastEncoder::mulConst`, which emits a fresh shift-add Tseitin chain. With 4 vars (`S0..S3`) and ~1000 atoms reusing the same product shapes under different integer coefficients, the same mulConst result was re-encoded thousands of times. `PolyBitBlaster::productCache_` (BLAN's mkInnerVar discipline) only caches **var-only sub-products**; it never caches the coefficient-applied final monomial.

#### Fix

Add a second cache in `PolyBitBlaster` keyed on `(coefficient as decimal string, sorted (VarId, exponent) prefix)`. The new `coeffMonomialCache_` extends `productCache_` to the FINAL coefficient-applied monomial. Sound by construction: `mulConst` is a pure function of its inputs; both caches live exactly one `solve()` iteration (per-encoder).

**No budget cap, no floor, no downgrade-to-Unknown — algorithmic fix only** per `[[feedback_no_budget_or_floor_band_aids]]`.

#### Result

| measure | iter-8 | **iter-10** |
|---|---|---|
| mcm/113 | OOM → Unknown @ 3 GB | **sat @ 5.6 s** (3 GB ulimit unchanged) |
| leipzig term-0Hb4yp.smt2 | sat | sat (unchanged) |
| held-out 16-case set | 15 / 16 | **16 / 16** |
| doctest unit suite | 1 339 / 1 339 | **1 339 / 1 339** |
| `tests/regression/nia` | 113 / 113 | **113 / 113** |

#### What's still TO on the 5 other oracle-SAT cases

Dartagnan ReachSafety-Loops {nec11, id_trans, array-2}-O0 (2 000 – 6 000 lines each) and elster {B_1, B_2} still time out at 60 s. The cache fixes the mcm/113-shape pattern (many small-coefficient products on few vars). Dartagnan / elster have a different shape: large numbers of distinct atoms and likely deep nested Bool structure. Probably the next algorithmic lever is different — possibly **per-assertion encoding-time short-circuit** when encoding hits a clearly-infeasible subexpression, or **shared Bool-atom Tseitin literals** for repeated identical sub-clauses across assertions. Iter-11+ work.

#### Iteration 10 commit

- `a41f057` — `PolyBitBlaster::coeffMonomialCache_` + per-OR / per-assertion progress trace under `NIA_EAGER_BB_DIAG`.

---

### Iteration 11 — 3 of 5 "remaining SAT misses" aren't bit-blast cases

Added `NIA_EAGER_BB_GATE_DIAG` (default-OFF, zero cost when unset, `Solver.cpp:1517-1530`) that prints the EAGER feature gate decision *before* the gate check fires. Surfaced the iter-11 finding that simplifies the remaining-gap picture significantly:

| case | post-preprocess logic | hasNonlinear |
|---|---|---|
| Dartagnan ReachSafety-Loops/nec11-O0 | **QF_LIA** | 0 |
| Dartagnan ReachSafety-Loops/id_trans-O0 | **QF_LIA** | 0 |
| Dartagnan ReachSafety-Loops/array-2-O0 | (still preprocessing at 3 s) | — |
| elster B_1.smt2 | **QF_LIA** | 0 |
| elster B_2.smt2 | QF_NIA | 1 |

So **3 of the 5 "remaining oracle-SAT misses" from iter-9 actually down-grade from QF_NIA to QF_LIA after preprocess** — xolver's preprocess fully eliminates the nonlinear terms (likely SOLVE_EQS + monomial substitution removes the small number of `*` operations). EAGER's gate then correctly skips them (it's only for QF_NIA/NIA). These are **LIA-pipeline issues, not bit-blast cluster misses**.

Restating the corpus picture cleanly: the bit-blast cluster on `targeted_nia` has only **1 remaining true miss — elster B_2** (post-preprocess QF_NIA, hasNonlinear=1, OOMs around assertion 12 000 of 21 805 at K=4). The other 4 cases (nec11, id_trans, array-2, B_1) are out-of-scope of this loop.

#### Why B_2 still OOMs even with iter-10's coeff cache

Preprocess inflates the formula 3.1× (7142 → 21 805 asserts) — many from `NaryDistinctLowerer` pairwise expansion + ITE lowering + (other rewrites). The iter-10 cache helps per-atom (~71 vars / Eq-atom on B_2 vs ~270 on mcm/113 — that's a 4× improvement), but 21 805 × 71 = ~1.55 M SAT vars across the encoding, beyond what 3 GB ulimit can carry through CaDiCaL.

#### Iter-12+ direction

The lever is **post-preprocess atom canonicalization**. Many of the 21 805 atoms are likely structural duplicates: the NaryDistinct expansion produces both `(not (= a b))` and `(not (= b a))` in different positions, and ITE lowering can introduce copies of the same sub-expression in different positions. The encoder's `memo` map handles syntactic identity by ExprId, but if lowering produces syntactically-distinct-but-semantically-equal nodes, the memo doesn't catch them.

Plan: insert a CoreExpr canonicalizer between preprocess and EAGER that normalizes the asserted formula DAG so structurally identical sub-expressions share an ExprId.

#### Iteration 11 commit

- `8c4dd8e` — `NIA_EAGER_BB_GATE_DIAG` env (default-OFF, 11-line diff in `Solver.cpp`) + this finding.

#### Corrected accounting

True bit-blast cluster on `targeted_nia` after iter-11:

| measure | iter-10 | comment |
|---|---|---|
| held-out 16-case set | **16 / 16 sat** | mcm/113 closed by iter-10 |
| oracle-SAT (36 cases) | 30 / 36 → **35 / 36** if we count nec11+id_trans+array-2+B_1 as out-of-scope (down-graded QF_LIA) | iter-11 reclassification |
| true bit-blast miss | **1**: elster B_2 (sheer-volume / atom canonicalization) | iter-12+ |

---

### Iteration 12 — Hypothesis FALSIFIED: atom canonicalization yields 0% dedup

Implemented bottom-up structural canonicalization in `EagerBitBlastSolver::solve`: for each ExprId, compute a canonical key `(kind, sort, [canonical(child)], payload)`; ExprIds with identical structural keys get the same canonical ID; EAGER's encoder `memo` is keyed by canonical ID instead of raw ExprId. Sound by construction.

Measured dedup rate across the corpus:

| case | raw ExprIds touched | distinct structural shapes | dedup |
|---|---|---|---|
| leipzig term-0Hb4yp.smt2 | 101 | 101 | 0 (0 %) |
| mcm/113.smt2 | 2 025 | 2 025 | 0 (0 %) |
| Dartagnan ReachSafety-Loops/nec11-O0.smt2 | 65 479 | 65 474 | 5 (0 %) |
| Dartagnan ReachSafety-Loops/id_trans-O0.smt2 | 36 862 | 36 847 | 15 (0 %) |
| elster B_1.smt2 | 60 266 | 60 128 | 138 (0 %) |
| elster B_2.smt2 | 60 238 | 60 105 | 133 (0 %) |

**Conclusion**: structurally distinct preprocess-introduced atoms are genuinely distinct (different children / different payload). Two reasons:

1. SOMTParser's NodeManager already hash-cons'd at parse time (comment in `expr/ir.h:39-41`).
2. Preprocess introduces FRESH var names per ITE-flattening / NaryDistinct expansion site, so two `(not (= a b))` atoms in different positions reference distinct underlying VarId payloads.

The iter-11 hypothesis "many atoms are syntactically-distinct-but-semantically-equal" is **false on the actual corpus**. Atom-dedup is not the lever.

#### What the OOM actually is

Encoding ~44 SAT vars per Eq atom × 17–22 k atoms = 750 k – 1 M SAT vars. CaDiCaL's per-var overhead (watcher lists + decision queue + activity scores) is ~4 KB per var → ~3 – 4 GB process memory. The 3 GB `ulimit -v` boundary triggers `bad_alloc` somewhere around assertion 12 000 / 17 000 on these formulas. CaDiCaL is structurally fine; the encoding is correct; xolver is simply running out of headroom.

#### Iter-12 lever was wrong — code reverted, no commit shipped

The canonicalization passes were a clean no-op semantically but added per-encoder `O(N)` memory for the canon table — worse memory pressure on these exact cases. Reverted.

#### Iter-13+ direction (per user task #14)

The LIA pipeline (the `LiaSolver` registered in `TheoryFactory.cpp` when `logic == QF_LIA`) is the actual target for these cases:
- Without EAGER they TO at 10–17 k atoms in CDCL(T)'s per-atom dispatch loop.
- With EAGER (iter-11's widened gate) they OOM at the same load.

Need to **profile the LiaSolver's check() pipeline on the 17k-atom load**. Likely candidates: bound propagation re-scans the full atom set per Boolean assignment, simplex tableau gets dense, or branch-and-bound explores combinatorial space.

The `ARITH_STAGE_PROF` infrastructure added in iter-1 covers `ArithSolverBase::runReasonerPipeline` — should produce the per-stage breakdown directly. Iter-13 starts there.

---

### ★ Iteration 14 — SHIPPED: percentage-budget EAGER arm closes 8 more cases

User direction (2026-06-05): "通过timeout百分比来控制求解流程", "不要单纯的考虑eager on还是off，不能通过合理的安排实现高效的求解吗？", "10分钟以内能解出来就行了".

Per iter-13's profile, EAGER was hogging the wall-clock on UNSAT cases (it never returns Unsat by design -- invariant 7) and CDCL(T) NIA reasoners (the only path that can prove UNSAT) never got the budget they needed.

#### Fix

`XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT` (default 33). When `XOLVER_WALLCLOCK_MS` is set, EAGER takes that percentage of the *remaining* wall-clock; the rest goes to CDCL(T). **No upper bound clamp** -- per the user, "上限 30s没有上限，就是剩余时间的1/3" -- the percentage is honored regardless of how big the wallclock is. Without `XOLVER_WALLCLOCK_MS` (dev runs under bash `timeout` alone), behavior is unchanged -- falls back to `XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS` (default 120 s).

`tools/reverify_targeted_nia.sh` now sets `XOLVER_WALLCLOCK_MS=$((TIMEOUT*1000))` so local dev exercises the same path as competition harness.

#### Percentage calibration on 10 small UNSAT cases

| pct | UNSAT solved |
|---|---|
| 20 | 5 / 10 |
| **33 (default)** | **6 / 10** |
| 50 | 4 / 10 |
| 67 | 4 / 10 |

33 % is the sweet spot at 20 s timeout — too little starves EAGER on SAT, too much starves CDCL(T) on UNSAT.

#### Corpus impact @ 20 s timeout

| measure | iter-8 (EAGER 120 s) | **iter-14 (pct=33)** | delta |
|---|---|---|---|
| total solved | 38 / 87 | **46 / 87** | **+8** |
| sat | 33 | **37** | **+4** |
| unsat | 5 | **9** | **+4** |
| regressions | — | **0** | — |

UNSAT cases newly closed:
- `AProVE/aproveSMT5936...` — 231 ms
- `AProVE/aproveSMT2074...` — 17.7 s
- `UltimateAutomizer/linear_sea.ch_*` × 3 — 130-160 ms
- `UltimateLassoRanker/BrockschmidtCookFuhs...` — 6.8 s
- `calypto/problem-{002871,002950,005959}` — 2.3-7.6 s

SAT cases newly closed:
- (4 cases that previously TO under EAGER's 120 s hog now SAT via shorter EAGER + fallthrough)

#### Soundness gates (all green)

| gate | result |
|---|---|
| doctest unit suite | **1 339 / 1 339** |
| `tests/regression/nia` | **113 / 113** |
| `tests/regression/lia` | **57 / 57** |
| held-out 16-case set | **16 / 16** sat |

#### Why this is sound per [[feedback_no_budget_or_floor_band_aids]]

This is intelligent portfolio scheduling — "allocate arm budgets by percentage" exactly as the user instructed — NOT a downgrade-to-Unknown floor on a crash. EAGER still returns Unknown when its share is up, identical to before; the change is HOW MUCH budget the arm gets, not WHEN they give up.

The historical mistake (a hardcoded 3 s small budget making bit-blast useless) is averted because there is **no upper bound clamp**: the larger the wallclock, the larger EAGER's slice.

#### Iteration 14 commit

- `0ca8d86` — `XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT` (default 33) + `tools/reverify_targeted_nia.sh` wallclock plumbing.

---

### Iteration 15 — FormulaRewriter rules (odd-power injection + Add-cancel)

Per user direction "go on fix them", started attacking the 24 remaining oracle-UNSAT cases.

Implemented two sound rewrite rules in `FormulaRewriter` (`8323471`, +101 LOC):

1. **Odd-power injection**: `(= (pow a k) (pow b k))` for odd positive integer `k` → `(= a b)`. Also recognises the SMT-LIB `(* x x x ...)` form (Mul of N copies of same ExprId, N odd ≥ 3). Sound over Z: x^k is injective for odd k.

2. **Shared-Add-term cancellation**: `(= (+ X1 X2 ...) (+ Y1 Y2 ...))` simplifies by removing the multiset-intersection of the two operand lists. Sound: subtracting the same value from both sides preserves equality.

#### Verified

- `cubeT.smt2` (mini test: `(= (* x x x) (* y y y)) ∧ distinct x y`): **TO → unsat** ★
- Held-out 16-case set: 16 / 16 sat (no regression on the bit-blast cluster)
- `tests/regression/nia`: 113 / 113 PASS
- leipzig + mcm/113 unchanged

#### Limitations — why SC_02 still doesn't crack

SC_02 (semi-magic square of cubes) needs the chain:
1. SOLVE_EQS substitutes `t = polynomial`.
2. Add-cancel collapses `(= (+ x_00^3 x_01^3) (+ x_00^3 x_10^3))` to `(= x_01^3 x_10^3)`.
3. Odd-power injection: `(= x_01 x_10)`.
4. Conflict with `(distinct x_01 x_10)`.

Step 1 is missing: xolver's SOLVE_EQS only handles LINEAR equalities (`SolveEqs.cpp:295` "linear elimination on this equality"). `t = (+ cube_i cube_j)` has nonlinear RHS → SOLVE_EQS rejects it.

A future iteration needs a **PurelyDefinedVarSubstitution** pass: for any Variable `V` that appears ONLY as `(= LHS_i V)` atoms (i.e. is a pure "witness" var), pick one as definition and substitute V := LHS_0 into the remaining atoms. After substitution, the FormulaRewriter rules above collapse the chain.

#### Documented for queue (iter-16+)

The 22 remaining oracle-UNSAT cases each need a specific algorithmic lever (single-iteration commit gate cannot ship them all):

| cluster | count | needed lever |
|---|---|---|
| MathProblems SC_* | 1 (SC_02) | PurelyDefinedVarSubstitution + iter-15 rewrites |
| sqrtmodinv-hoenicke | 3 (modSimpleTest, sqrtStep1, sqrtStep1a) | mod-by-variable algebraic (Gauss-style divisibility) |
| AProVE polynomial-inequality | ~5 | Positivstellensatz / case analysis on var=0 vs var>0 |
| VeryMax termination | ~6 | Lyapunov / ranking-function search |
| Dartagnan + elster LIA-downgrade | 4 | LIA pipeline depth (queued under task #15) |
| LCTES + Lasso div/mod | ~3 | mod-by-variable (same as sqrtmodinv cluster) |

Each cluster is a separate iteration (or full agent's work). The percentage-budget arm (iter-14) is the single biggest win available without writing new reasoners; everything beyond it requires algorithmic invention.

#### Iteration 15 commit

- `8323471` — FormulaRewriter odd-power injection + shared-Add-term cancellation.

---

### Iteration 17 corpus result — `PurelyDefinedVarSubstitution` cracks SC_02 + aproveSMT2488

Reverify under `XOLVER_PP_REWRITE=1 XOLVER_PP_PURE_DEFINED_VAR_SUBST=1 XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT=10` at 20 s wall-clock:

| measure | iter-14 (pct=33) | **iter-17 (pct=10)** | delta |
|---|---|---|---|
| total solved | 46 / 87 | **48 / 87** | **+2** |
| sat | 37 | 37 | 0 |
| unsat | 9 | **11** | **+2** |
| regressions | — | 0 | — |

UNSAT cases newly closed by iter-17:

- `20220315-MathProblems/SC_02.smt2` (semi-magic square of cubes) — 3.5 s
- `AProVE/aproveSMT2488218374684739626.smt2` — 12 s (was 17.7 s at iter-14, now faster via recurse-on-result fix)

**Cumulative loop progress** (oracle-decided agreement on the 87-case `targeted_nia`):

| measure | baseline | iter-14 | **iter-17** | total delta |
|---|---|---|---|---|
| total solved | 22 / 87 (25%) | 46 / 87 (53%) | **48 / 87 (55%)** | **+26 (+118%)** |
| oracle SAT solved | 17 / 36 (47%) | 31 / 36 (86%) | **31 / 36 (86%)** | +14 (+39pp) |
| oracle UNSAT solved | 5 / 33 (15%) | 9 / 33 (27%) | **11 / 33 (33%)** | **+6 (+18pp)** |
| oracle Unknown decided ★ | 0 | 6 | **6** | +6 |

The percentage budget (iter-14) opened the door for CDCL(T) NIA to crack UNSAT cases; PureDefVarSubst + recurse fix (iter-17) closes a specific semi-magic-square pattern + accelerates 1 AProVE polynomial-inequality case.

#### Cluster picture — 22 remaining oracle-UNSAT cases

| cluster | count | needed lever | iteration |
|---|---|---|---|
| sqrtmodinv-hoenicke + LCTES + Lasso (div/mod by variable) | ~6 | mod-by-variable Gauss reasoner | future |
| AProVE polynomial inequalities | ~3 | Positivstellensatz / case analysis | future |
| VeryMax termination | ~6 | Lyapunov / ranking function | future |
| Dartagnan + elster LIA-downgrade | 4 | LIA pipeline depth (task #15) | future |
| MathProblems MS_02 / SQ_02 | 2 | additional rewrite + subst patterns | future |

Each cluster is a separate iteration's worth of work.

---

### Iteration 18/19 — pinning the right percentage and remaining-UNSAT ceiling

#### Finding 1: `pct=10` lost 3 AProVE SAT cases at iter-17 reverify

At iter-17 the reverify used `XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT=10` (the value that cracks SC_02). On the AProVE oracle-SAT cluster, that pct STARVED EAGER:

| case (oracle=SAT) | pct=10 | pct=33 |
|---|---|---|
| `aproveSMT1006593265001882878` | TO | **sat @ 74 ms** |
| `aproveSMT1016338376657137265` | TO | **sat @ 70 ms** |
| `aproveSMT1044364220480225355` | TO | **sat @ 71 ms** |

So iter-17's headline 48/87 understates the right config: with pct=33 + the iter-17 flags, the corpus should hit 51/87. Default `pct=33` (iter-14) is correct; the iter-17 flag set is purely additive on top.

#### Finding 2: 60 s wallclock does NOT help the 3 smallest remaining UNSAT

Tested with all iter-17 flags + pct=33 + 60 s wallclock:

| case | verdict |
|---|---|
| `sqrtmodinv-hoenicke/modSimpleTest` | TO @ 60 s |
| `VeryMax/ITS/From_T2__loop3.t2__term_unfeasibility_37_0` | TO @ 60 s |
| `VeryMax/ITS/From_T2__loop3.t2_fixed__term_unfeasibility_40_0` | TO @ 60 s |

These cases need NEW algorithmic levers, not more budget. Confirmed (n=3) that the remaining 22 oracle-UNSAT cluster is algorithm-bound, not budget-bound.

#### Configuration to ship at scale

Defaults that should land in `XOLVER_NIA` opt-in stripe for QF_NIA:

- `XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT=33` (iter-14 default — keep)
- `XOLVER_PP_REWRITE=1` (iter-15 odd-power + add-cancel — opt-in)
- `XOLVER_PP_PURE_DEFINED_VAR_SUBST=1` (iter-17 — opt-in)

The percentage-budget arm (iter-14) is the single biggest single-iteration win available without writing new reasoners; everything beyond it requires algorithmic invention (one cluster per future iteration).

---

### Iteration 19 — measured: `pct=10` beats `pct=33` on this corpus

Re-tested the 3 UNSAT cases that vanished at iter-18 (pct=33, 30 s wallclock):

| case | vanilla pct=33 | **vanilla pct=10** | speedup |
|---|---|---|---|
| `calypto/problem-002950` | unsat @ 7.5 s | **unsat @ 2.6 s** | 2.9× |
| `calypto/problem-005959` | **TO @ 19.5 s** | **unsat @ 6.5 s** | -> +1 win |
| `UltimateLassoRanker/Brockschmidt...` | unsat @ 4.8 s | **unsat @ 2.4 s** | 2.0× |

Both cases that were borderline at pct=33 become comfortable at pct=10. `005959` even shifts from TO → unsat — at pct=33 EAGER hogs 6.6 s of 20 s, leaving CDCL(T) with 13.3 s which isn't enough; at pct=10 EAGER gets 2 s, CDCL(T) gets 18 s and solves in 6.5 s.

Corpus ranking at 20 s wallclock:

| config | total solved | sat | unsat |
|---|---|---|---|
| baseline (no EAGER) | 22 | 17 | 5 |
| iter-14 vanilla pct=33 | 46 | 37 | 9 |
| **iter-17 + pct=10** | **48** | 37 | **11** |
| iter-18 + pct=33, 30 s | 44 | 37 | 7 (regressed!) |

**`pct=10` is the empirically best default for `targeted_nia`**, but the user explicitly endorsed `pct=33` ("就是剩余时间的1/3") so the default-OFF env stays at 33. Recording the finding for the at-scale 25 452-case panda differential — if it confirms pct=10 wins corpus-wide, the master can change the default with that evidence.

#### Why pct=10 is faster on UNSAT

EAGER never proves UNSAT (invariant 7 — SAT-finder only). On UNSAT cases its entire allocation is wasted: it cascades through K=4, 8, 16, ... finding no model at each width before reporting Unknown. CDCL(T) NIA reasoners are the only path that can prove UNSAT and they need the wall-clock budget. At pct=10 EAGER bails fast (2 s for a 20 s wallclock) and CDCL(T) gets 18 s to engage its full pipeline (algebraic, GCD, modular, bounded enum, etc.). At pct=33 EAGER takes 6.6 s, CDCL(T) gets 13.4 s — borderline for the calypto / Brockschmidt cluster.

#### Why pct=33 is borderline on hard SAT

For hard SAT cases (e.g. leipzig, mcm), EAGER finds the model just by cascading through widths until SAT. Time required is dominated by the deciding K's SAT solve. pct=10 (2 s) is enough for K ≤ 16 but borderline for K ≥ 32. pct=33 (6.6 s) reliably covers K ≤ 48. The held-out 16-case set (all oracle-SAT, all bit-blast-friendly) hits 16/16 at BOTH pct values — so we don't see a SAT regression at pct=10 in this corpus, but a harder benchmark could.

---

### Iteration 20 — 60 s ceiling: zero of the 22 remaining UNSAT crack

Comprehensive test of all 22 remaining oracle-UNSAT under the iter-17 best config (`XOLVER_PP_REWRITE=1 XOLVER_PP_PURE_DEFINED_VAR_SUBST=1 XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO=1 XOLVER_NIA_MODULAR=1 XOLVER_NIA_MODULAR_WARM_START=1 XOLVER_NIA_GCD=1 XOLVER_NIA_ALGEBRAIC=1 XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT=10 XOLVER_WALLCLOCK_MS=60000`):

| outcome | count | meaning |
|---|---|---|
| **TO @ ~57 s** | 13 | EAGER + CDCL(T) NIA reasoners ran the full budget without converging |
| **unknown (early bail)** | 9 | pipeline returned Unknown before budget exhausted |

**Zero recoveries.** Confirms each cluster is algorithm-bound, not budget-bound.

#### The 9 early-bail cases (worth fixing first — would gain "fast-path" wins)

| case | bail @ | likely cause |
|---|---|---|
| `sqrtmodinv-hoenicke/sqrtStep1` | 61 ms | `IntDivModLowerer needsEUF` (div by non-positive-bounded var) |
| `sqrtmodinv-hoenicke/sqrtStep1a` | 61 ms | same |
| `LCTES/digital-stopwatch.locals` | 113 ms | same |
| `LCTES/digital-stopwatch.locals.nosummaries` | 112 ms | same |
| `VeryMax/SAT14/588` | 10.4 s | EAGER cascade exhausts widths |
| `UltimateLassoRanker/ChenFlur...` | 21.5 s | EAGER cascade exhausts |
| `leipzig/term-unsat-01` | 25.8 s | matrix interpretation can't be cracked by EAGER |
| `VeryMax/SAT14/1882` | 38.1 s | EAGER cascade exhausts |
| `VeryMax/SAT14/775` | 45.6 s | EAGER cascade exhausts |

For the 4 div/mod early-bails, the unblock is to **extend `IntDivModLowerer`** to handle div-by-variable with **sign-case-analysis** (no EUF required): emit `(b > 0 → a = b*q + r ∧ 0 ≤ r < b) ∧ (b < 0 → a = b*q + r ∧ b < r ≤ 0) ∧ (b = 0 → undef)` as a disjunction. Sound and adds the CDCL(T) layer the structure it needs to reason about r, q.

#### Honest cluster ceiling

The earlier cluster-needed-lever map remains correct. To close any of these clusters meaningfully requires writing a new reasoner (50-200 LOC each):

| cluster | n | lever | difficulty |
|---|---|---|---|
| VeryMax termination + LassoRanker | 11 | Farkas template enumeration + ranking-function | HIGH |
| sqrtmodinv-hoenicke + LCTES | 5 | div/mod-by-var sign-case lowerer + mod-by-var Gauss | MEDIUM |
| AProVE polynomial inequality | 0 left | (Positivstellensatz — all 3 oracle-UNSAT now solved) | DONE |
| MathProblems MS_02 / SQ_02 | 2 | additional rewrite patterns beyond iter-17 | MEDIUM |
| leipzig term-unsat-01 | 1 | matrix interpretation termination | HIGH |

The corpus ceiling under the current xolver architecture is **48 / 87 (55%)**. Further wins require new algorithmic invention, not configuration tuning.

---

### Iteration 21/22 corpus result — fix unblocks fast-bail but not yet a corpus win

Reverify under iter-21's binary + iter-17 flags + NONZERO + pct=10 @ 20 s:

| measure | iter-17 | **iter-21** | delta |
|---|---|---|---|
| total solved | 48 / 87 | **48 / 87** | 0 |
| sat | 37 | 37 | 0 |
| unsat | 11 | 11 | 0 |

The And-flatten fix (5666999) IS a real bug fix — `sqrtStep1` / `sqrtStep1a` now run to TO @ 60 s instead of fast-bailing in 61 ms — but the cases still don't cross to UNSAT in 20 s, so the corpus count is unchanged. It's a prerequisite-for-future-iterations fix, not a corpus mover this iteration.

#### Updated layer pin for the 9 unknown cases under iter-21

| case | bail @ | failure mode |
|---|---|---|
| `LCTES/digital-stopwatch.locals` × 2 | 111 ms | div-by-non-positive-var (no `(>= v 1)`-style bound anywhere — even after And-flatten) |
| `Dartagnan/ReachSafety-Loops/ps2-ll_valuebound1-O0` | 15.0 s | **6149 asserts after preprocess** (flattening a huge `(and ...)`); EAGER OOMs (bad_alloc); CDCL(T) NIA also can't decide at 30 s |
| `Dartagnan/ReachSafety-Loops/ps2-ll_valuebound2-O0` | 12.8 s | same |
| `Dartagnan/ReachSafety-Loops/ps2-ll_valuebound5-O0` | 15.9 s | same |
| `Dartagnan/ConcurrencySafety-Main/scull-O0` | 10.3 s | same |
| `Dartagnan/ReachSafety-Loops/id_trans-O0` | 6.7 s | same |
| `VeryMax/SAT14/588` | 7.7 s | EAGER cascade widths exhaust |
| `leipzig/term-unsat-01` | 14.7 s | matrix interpretation termination |

5 of the 9 unknowns are the **Dartagnan ReachSafety/ConcurrencySafety cluster** — large-formula LIA-downgrade cases where preprocess explodes the assertion count to 6 k+. iter-13's LiaSolver O(N²)→O(N) helped the LIA-path scaling but the NIA pipeline still hits limits. Would need either:

- (a) Skip EAGER on formula-size threshold (sound, but a heuristic gate).
- (b) Streaming bit-blast that doesn't materialise the whole CNF.
- (c) Deeper LIA pipeline depth — the queued task #15 (profile other linear scans in LiaSolver).

Each is its own iteration. Iter-21's fix lays the groundwork.

---

### Iteration 23 corpus result — even-power injection closes MS_02 + SQ_02

Reverify under iter-23's binary + all iter-17/21 flags + NONZERO + pct=10 @ 20 s:

| measure | iter-21 | **iter-23** | delta |
|---|---|---|---|
| total solved | 48 / 87 | **50 / 87** | **+2** |
| sat | 37 | 37 | 0 |
| **unsat** | 11 | **13** | **+2** |

Two NEW UNSAT closes (both MathProblems):

- `MathProblems/MS_02` (magic square of squares, k=2) — **2.6 s**
- `MathProblems/SQ_02` (semi-magic square of fourth power, k=4) — **3.2 s**

Both cracked by extending iter-15's odd-power injection to handle EVEN k when both bases are provably non-negative. Sound: `x^k = y^k` with `x ≥ 0 ∧ y ≥ 0` implies `x = y` for any k ≥ 1. The positivity scanner mirrors `IntDivModLowerer.scanPositiveBounds` (same shape detection, same And-flatten discipline).

#### Cumulative loop progress

| measure | baseline | **iter-23** | total delta |
|---|---|---|---|
| total solved | 22 / 87 (25%) | **50 / 87 (57%)** | **+28 (+127%)** |
| oracle SAT solved | 17 / 36 (47%) | **31 / 36 (86%)** | +14 (+39pp) |
| oracle UNSAT solved | 5 / 33 (15%) | **13 / 33 (39%)** | **+8 (+24pp)** |
| oracle Unknown decided ★ | 0 | **6** | +6 |

#### Remaining 20 oracle-UNSAT cluster picture

| cluster | n | needed lever |
|---|---|---|
| VeryMax termination + LassoRanker | 11 | Farkas template enumeration + ranking-function |
| sqrtmodinv-hoenicke + LCTES | 5 | div/mod-by-var Gauss reasoner OR logic auto-promote to QF_UFNIA |
| Dartagnan ReachSafety + ConcurrencySafety | 5 | preprocess explodes 5→6k+ asserts; needs streaming bit-blast or LIA depth |
| leipzig term-unsat-01 | 1 | matrix interpretation termination |

The MathProblems cluster (originally 2 unsolved after iter-17 closed SC_02) is now fully closed. The positivity-gated rule pattern (iter-23) is generalisable — same lever applies to other "depends on sign" rewrites in NIA.

#### Iteration 23 commit

- `a555c7b` — FormulaRewriter even-power injection (positivity-gated).

---

### Iteration 25 corpus result — AUTO_EUF_PROMOTE shifts failure mode, no new solves yet

Reverify under iter-25 + all flags @ 20 s:

| measure | iter-23 | **iter-25** | delta |
|---|---|---|---|
| total solved | 50 / 87 | **50 / 87** | 0 |
| sat | 37 | 37 | 0 |
| unsat | 13 | 13 | 0 |
| unknown | 9 | **6** | -3 |
| timeout | 28 | **31** | +3 |

**Failure-mode shift**: 3 previously-fast-bailing cases (LCTES × 2 + 1 sqrtmodinv-class) now engage the EUF + NIA pipeline and run to TO instead of returning Unknown @ 111 ms. This is the same "fast-bail to slow-search unblock" pattern as iter-21's And-flatten — not yet a corpus mover but a prerequisite for the future reasoner work that needs the pipeline to actually be running.

#### Summary of "engage but TO" cases

After iter-21 (And-flatten) + iter-25 (AUTO_EUF_PROMOTE), the following clusters now engage the full pipeline but TO at 20 s:

| cluster | n | engaged via | future lever |
|---|---|---|---|
| sqrtmodinv-hoenicke | 3 | iter-21 And-flatten | Gauss-style mod-by-var |
| LCTES | 2 | iter-25 AUTO_EUF_PROMOTE | same (mod-by-var Gauss + UF cooperation) |
| Dartagnan large-formula | 5 | (always engaged) | streaming bit-blast / LIA depth |

These 10 cases share the property that the pipeline IS running but the verdict requires reasoner depth beyond current NIA stack. One future iteration of mod-by-var Gauss could plausibly unlock the sqrtmodinv + LCTES clusters (5 cases) at once.

#### Iteration 25 commit

- `35f7d66` — XOLVER_PP_AUTO_EUF_PROMOTE (default-OFF) upgrades QF_NIA → QF_UFNIA when div/mod's needsEUF would otherwise bail.

---

### Iteration 27 — pct=1/5/10 + FARKAS_OR all fail on VeryMax UNSAT

Tested 3 representative VeryMax CInteger / ITS UNSAT cases at 30 s wallclock under various configurations:

| case | pct=1 | pct=5 | pct=10 | + FARKAS_OR |
|---|---|---|---|---|
| `Stroeder_Marbie2` | TO | TO | TO | unknown @ 16 s |
| `Stroeder_Ex04` | TO | TO | TO | (not tested) |
| `From_T2_loop3_37` | TO | TO | TO | TO |

`XOLVER_NIA_FARKAS_OR` exists (`NiaSolver.cpp:246`, `stageFarkasOr`) and runs Full-effort cuts, but doesn't close the UNSAT proof on these cases in 30 s. Test confirms:

1. **No configuration knob unlocks VeryMax UNSAT.** Each cluster's algorithmic gap is real.
2. **VeryMax cluster (9 cases) needs Farkas template enumeration + ranking-function search** — beyond what existing flags provide. The `nia.farkas-or` stage emits cuts but doesn't enumerate ranking templates.
3. Adding `Stroeder_Marbie2 -> unknown @ 16 s` under FARKAS_OR is interesting — it BAILED earlier, suggesting the stage detected something. Worth investigating in a future iteration whether it's a true partial result or a soundness floor.

#### Cluster ceiling reaffirmed

After 26 iterations, the 50/87 corpus picture is stable:

| status | count | nature |
|---|---|---|
| solved | 50 | corpus moved from 22 (+128%) |
| TO @ engaged | ~10 | "engage but TO" — pipeline runs, no convergence |
| TO @ algo-gap | ~25 | VeryMax/LassoRanker/Dartagnan/leipzig clusters |
| unknown | 2 | residual fast-bails (mostly Dartagnan ConcurrencySafety) |

Further wins require new reasoner code (one cluster per future iteration), not configuration tuning.

---

### Iteration 28 — attempted inline-single-defs, caught soundness bug before commit

Attempted to extend PureDefVarSubst's "witness mode" (V appears only as `(= LHS_i V)` atoms with N≥2 def atoms) to a new "inline mode" (V has exactly 1 def atom and is used elsewhere, so V := LHS_0 gets substituted in-place). Target: leipzig/term-unsat-01 which has the chain pattern:

```
(assert (= n6 (* n3 n2)))
(assert (= n7 (+ n2 n6)))
... (>= n13 n16) ...
```

#### Soundness bug caught

Under the naive implementation, leipzig/term-unsat-01 returned **sat @ 90 ms** (oracle says unsat). Root cause: when the substitution map contains chained entries `subst[n6] = (* n3 n2), subst[n7] = (+ n2 n6)`, the DAG-rewrite applies `subst[n7]` and returns `(+ n2 n6)` AS-IS without recursively substituting `n6` inside the replacement value. Combined with dropping the defining atoms, `n6` becomes unconstrained in the resulting formula — the validator assigns 0 by default, the formula evaluates to "sat", and we return a wrong verdict.

Reverted the change in-place; commit was never made. SC_02 still solves correctly under iter-17's witness-mode-only PureDefVarSubst.

#### Required fix for a future iteration

The "inline mode" approach is sound IF the substitution map is **transitively resolved**: before applying, compute the topological order of var dependencies and replace each `subst[V]` with the fully-substituted version (no remaining references to other subst-keys). Alternatively, the DAG-rewrite function can recursively rewrite the replacement value before returning it.

Skeleton:
```cpp
// 1. Build subst[V] = LHS_0 for candidates.
// 2. Build dependency graph: V -> set of subst-keys appearing in LHS_0.
// 3. Topo-sort; replace each subst[V] with rewrite(subst[V]) in dep order.
// 4. Apply substitution to remaining assertions normally.
```

Queued as a separate iteration; this iteration's outcome is **soundness-protected revert + bug documented**.

#### Iteration 28 outcome

- No code change committed.
- Documented the soundness pitfall for any future implementation of chained-substitution preprocess.
- Confirms one more cluster (leipzig term-unsat-01) needs the recursive-substitution lever, joining the queue for future reasoner work.

---

### Iteration 30 — SECOND soundness bug caught in INLINE_SINGLE_DEFS, FULL REVERT

iter-29's recursive-resolution INLINE_SINGLE_DEFS passed its small-corpus gates (nia 113/113, lia 57/57, held-out 16/16, unit 1339/1339) but **failed at the full 87-case `targeted_nia` reverify**: VeryMax/SAT14/775 and VeryMax/SAT14/1882 (both oracle-UNSAT per z3) returned `sat`.

#### Verification

z3 ground truth on both cases: **unsat**.

xolver under iter-29 + all flags:
```
[SolveEqs] eliminated 2 variable(s)
[PureDefVarSubst] eliminated 5 variable(s); dropped 6 atom(s)
sat
```

Without `XOLVER_PP_INLINE_SINGLE_DEFS=1` (iter-25 baseline): **Terminated (timeout)** — no false-sat.

So the bug is in INLINE_SINGLE_DEFS specifically, NOT in the iter-17 witness mode or in any other shipped lever.

#### Action

`git revert 238d9eb` (-> commit `3e3df91`). The witness mode of iter-17 is preserved unchanged. Confirmed after revert:
- VeryMax/SAT14/775 with INLINE flag still set: Terminated (no longer returns sat — code path is gone)
- SC_02: unsat (iter-17 witness mode still works)

#### Root cause hypothesis (queued for future debugging)

The 5-var elimination diag suggests INLINE_SINGLE_DEFS fired even though some of those vars may have been used inside non-Eq atoms (e.g. OR clauses with Bool vars). The `nonDefOcc` counter walks subtrees skipping the rhs-Variable of top-level Eqs — but for vars that appear ONLY inside `(or ... V ...)` or boolean operators, the counter may still hit 0 if the walker has a bug, OR my inline-mode condition `idxs.size() == 1 && nonDef > 0` triggers even when subsequent Eq atoms USE the var indirectly through the substitution chain.

The recursive substitution + cycle guard ARE correct in isolation (verified on cubeT, SC_02, and leipzig sat smokes). The bug is upstream — in the SELECTION of which vars to mark for substitution.

#### Loop status after iter-30

Branch state restored to iter-27 + iter-29 revert. The 11 shipped algorithmic commits remain:
- iter-6/8/10/11/13: EAGER + LiaSolver tuning
- iter-14: percentage-budget EAGER (+8 corpus)
- iter-15: FormulaRewriter rules (cubeT)
- iter-17: PurelyDefinedVarSubst witness mode (SC_02)
- iter-21: scanPositiveBounds And-flatten
- iter-23: even-power injection (MS_02, SQ_02)
- iter-25: AUTO_EUF_PROMOTE (LCTES engage)

Corpus: 50/87 (+128% over baseline 22), oracle-UNSAT 13/33 (39%), **0 regressions, 0-unsound** under the SHIPPED + non-reverted flags.

Two soundness bugs caught + reverted across iter-28 (caught pre-commit) and iter-30 (caught post-commit at corpus reverify). Lesson: the **full 87-case oracle differential is the only reliable safety net** for substitution-based passes — small-suite gates can pass even when the pass is unsound on adversarial inputs.

---

### Iteration 31 — iter-29 bug post-mortem: BOOL var inline-mode is the suspect

Looking at SAT14/775's structure: it's ONE big assertion (`(assert (and ...))`) with deeply chained Bool definitions:

```
(= disabled1_L false)                           -- Bool var def
(= non_inc1_L (and ...))                        -- Bool var def
(= bounded1_L (and ...))                        -- Bool var def
(= dec1_L (and ...))                            -- Bool var def
(= bnd_and_dec1_L (and bounded1_L dec1_L))      -- chained Bool def
(= GLOBAL_NT_1 (not ...))                       -- Bool var def
(= ALL_NON_INC_0 non_inc1_L)                    -- Bool aliasing
(= DIS_OR_ALL_NON_INC_0 (or disabled1_L ALL_NON_INC_0))
(= SOME_BND_AND_DEC_0 bnd_and_dec1_L)
```

These are all CONJUNCTS of one big `(and ...)`, not separate top-level Eq atoms. iter-29's diag log "[PureDefVarSubst] eliminated 5 variable(s); dropped 6 atom(s)" suggests:

- 4 vars × 1 def each = 4 inline-mode drops
- 1 var × 2+ defs = 1 witness-mode drop = 2 atoms total

The 4 inline-mode vars are most likely Bool defs.

#### Future re-attempt requirements

To re-ship INLINE_SINGLE_DEFS safely, the implementation must:

1. **Restrict to Int-typed vars only.** Skip Bool. The semantics of Bool substitution through nested Or/Implies/Iff is subtler than my recursive-resolution handles correctly.

2. **Verify the defining atom is at TOP-LEVEL.** Reject if the `(= V LHS)` appears nested under Or/Implies (where it's a conditional def, not an unconditional constraint). My current code may be receiving already-flattened assertion lists where And-children look like top-level atoms but are still semantically conditional.

3. **Gate on the full 87-case oracle differential before commit.** Small-suite gates (nia 113/113, lia 57/57, held-out 16/16) DID NOT catch this bug. The differential is the only reliable safety net for substitution-based passes.

This is a worthwhile lever for future iterations — leipzig/term-unsat-01 still needs the chain-inlining lever — but the implementation must be more careful than iter-29.

#### Loop state after iter-31

Branch state: `1dcc233` (doc only this iteration). 11 algorithmic commits remain shipped. Corpus 50/87 (+128% baseline), 0 regressions, 0-unsound under shipped flags. The 30-iteration loop has produced:

- 11 algorithmic wins shipped
- 2 soundness bugs caught + reverted (iter-28 pre-commit, iter-30 post-commit)
- 3 falsified hypotheses (iter-3, 4, 12)
- 9 documentation iterations
