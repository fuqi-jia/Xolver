# Phase A Report — preprocess-deep (cross-division frontend gap)

**Branch:** `agent/preprocess-deep` (base `origin/integration` @ 3a56619)
**Data:** `results/2026-05-31/full.sqlite` (70540 cases, 10-panda batch on integration 3a56619)
**Oracle:** z3 4.13.0 (+ cvc5 for DT). Local benchmark mirror: `NLColver/benchmark/non-incremental/`.
**Binary used for diagnosis:** main worktree `build/bin/xolver` @ 3a56619 (same commit as my base).

---

## TL;DR (read this first)

| assigned target | gap | verdict mix | Phase-A finding | preprocessing lever? |
|---|---:|---|---|---|
| **QF_NIA VeryMax/SAT14** | 1635 | 1574 sat / 61 unsat | **engine-bound, NOT preprocessing-bound** | ❌ low ceiling — needs NLA |
| **QF_LIA convert** | 220 | **219 sat** / 1 unsat | **clean var-elim win** — `PP_SOLVE_EQS` already flips cases, 0 unsound, default-OFF | ✅ **primary** |
| QF_LIA rings_preprocessed | 142 | **0 sat / 142 unsat** | UNSAT-proving; var-elim does nothing | ❌ wrong lever |
| QF_NIA VeryMax/ITS | 4600 | 2468 / 2132 | shared w/ NIA; same NLA shape as SAT14 | ❌ defer to NIA |

**Recommendation: pivot the lane's Phase-B effort from SAT14 → QF_LIA `convert` (var-elimination strengthening + `PP_SOLVE_EQS` promotion).** SAT14 is the master's pre-pick, but the evidence below shows it is blocked by a *missing theory capability* (z3's NLA bound-propagation), not by formula size or CNF encoding. Preprocessing cannot supply reasoning xolver doesn't have; it can only shrink/route. `convert` is where pure simplification genuinely flips cases.

---

## 1. SAT14 deep diagnosis (the assigned cluster)

### 1.1 Shape of the gap
All 1635 unsolved SAT14 cases are `xolver default=timeout, allon=timeout`; oracle decides (1574 sat / 61 unsat). So this is dominantly a **model-finding** gap.

Size correlates but is **not** the binding constraint:
- SOLVED SAT14 (175 cases): avg **20 KB**
- UNSOLVED SAT14 (1751 cases): avg **59 KB**
- …but the *smallest* unsolved case, `86.smt2`, is **1978 bytes** (13 int vars) and still times out at 20 s. **A 2 KB instance failing kills the "formula too big" hypothesis as the root cause.**

### 1.2 What these instances are
VeryMax / Barcelogic **termination-proving (Farkas-lemma invariant synthesis)**. Structure (verified on `86.smt2`, `1018.smt2`):
- `lam*` = Farkas multipliers, many with **tiny forced domains** (`0≤x<1` over Int ⟹ `x=0`; `0≤x≤1` ⟹ `{0,1}`).
- `global_invc*` = invariant coefficients, several bounded `[-1,1]` = `{-1,0,1}`.
- Nonlinearity = **bilinear products** `lam·global_invc`. Sparse: `86.smt2` has only **3** var·var products; the 55 KB `1018.smt2` has **82** (no repetition) over **483 int vars**.

So large SAT14 files are large because of **many variables in a near-linear Farkas system**, with light bilinear coupling — not because of nonlinear blow-up.

### 1.3 Where xolver spends the time (gdb stack sampling, ptrace_scope=1 → child-launch + timer-SIGINT)
The solve runs in a worker thread; the hot stack is:
```
CaDiCaL::Closure::reset_closure / forward_subsume_matching_clauses / extract_gates   ← CaDiCaL BVE inprocessing
CaDiCaL::Internal::preprocess_quickly
xolver::CadicalBackend::solve
xolver::bitblast::BitBlastSolver::attemptAtWidths
xolver::bitblast::BitBlastSolver::solve
xolver::NiaSolver::stageBitBlast          ← terminal NIA reasoner stage
ArithSolverBase::runReasonerPipeline
CadicalTheoryPropagator::cb_check_found_model
```
**xolver falls through all 16 NIA reasoner stages to the terminal `nia.bit-blast` stage**, then bit-blasts the bilinear system. CaDiCaL grinds (≈89 % CPU, compute-bound) on the multiplier CNF — exactly the `extract_gates → find_equivalences` pathology already documented in `BitBlastSolver.cpp:178` for QF_UFNIA floored cases.

### 1.4 What z3 does instead (the missing capability)
`z3 86.smt2 -st` → **sat in 0.54 s, 40 decisions, 12 conflicts**, via the **NLA (nonlinear-LP) path**:
`arith-grobner-calls 9`, `arith-nla-lemmas 8`, `arith-nla-propagate-bounds 3`, `arith-nra-calls 4`, `arith-horner-calls 3`. **No bit-blasting.**
Satisfying model is small and *almost linear*: `lam1n4=0` (kills 2 of 3 products), `global_invc1_0=1` (3rd product → identity), `global_invc1_1=-114`, rest tiny. A bound-propagation + linearization engine finds this instantly.

### 1.5 Levers tested — none flip SAT14
| lever | 86.smt2 (2 KB) | 1018.smt2 (55 KB) |
|---|---|---|
| default | timeout | timeout |
| `PP_SOLVE_EQS` (var-elim) | timeout | timeout |
| `NIA_BITBLAST_NOPRE` (kill CaDiCaL BVE/extract_gates) | timeout | timeout |
| `NIA_BITBLAST_CONFLICTS=200k/500k` (cap each width) | timeout | timeout |

Disabling the exact CaDiCaL chain the gdb stack sits in **does not help** — so the cost is not only inprocessing; the bit-blast width cascade itself (re-encode 483 vars × K bits, climb K=2→64) is the wrong tool. **Conclusion: SAT14 needs an NLA/bound-propagation theory capability. Preprocessing has a low ceiling here. Route to the NIA lane; do not sink Phase-B effort into SAT14.**

---

## 2. The real preprocessing leverage: QF_LIA `convert` (PRIMARY Phase-B target)

`convert-jpg2gif` = pure QF_LIA, **219 sat / 1 unsat**, all weakness cases 70–78 KB, ~525 int vars, **260 equalities** (which linearly *define* many vars). z3 solves `convert-jpg2gif-query-1178` in **0.17 s**; xolver times out.

**`XOLVER_PP_SOLVE_EQS=1` (linear equality var-elimination, currently default-OFF) flips these:**

```
12 convert weakness cases (oracle-decided, xolver-timeout), PP_SOLVE_EQS @20s:
  RECOVERED = 3/12   UNSOUND = 0
  (1178 sat, 1182 sat, 1201 sat recovered; 9 still timeout at 20s)
```

This is the clean, in-lane, in-charter win: the flag exists, it is sound here (0 unsound across the convert sample), and it is held back only by being default-OFF (historical reason: model-reconstruction incompleteness → some cases floored to `unknown`). The 9 that still time out at 20 s are the Phase-B work: either (a) the reconstruct gate is too conservative and skips eliminable vars, or (b) elimination isn't aggressive enough and the residual LIA is still hard.

### Why rings_preprocessed (142) is *not* a var-elim target
All **142 are UNSAT**. `PP_SOLVE_EQS` recovers 0/4 (all timeout). Var-elimination helps SAT-model search and equality chains, not UNSAT-proving of modular ring constraints (`ring_2exp12_4vars_3ite_unsat`). These need different reasoning (modular/cutting-plane) — lower preprocessing leverage; deprioritize.

---

## 3. Revised Phase-B / Phase-C plan

**Phase B (primary): strengthen + de-risk `PP_SOLVE_EQS` for the convert cluster.**
1. Diagnose the 9 still-timeout convert cases: is it the reconstruct gate (eliminable vars skipped) or residual hardness? Instrument elimination count.
2. Widen the gate / fix model reconstruction so more linear-defined vars are eliminated **without** the soundness floor that forced default-OFF (the A5-lane reason). Keep the existing reconstruct-fail→`Sat`→`unknown` floor as the safety net.
3. Independent commit, `XOLVER_*` flag convention, double gate (reg OFF+ON, full unit suite).

**Phase B (secondary, if time): a bounded interval/bound-propagation prepass** as a *poor-man's NLA* for the Farkas SAT14/ITS subset — forward+reverse bound propagation through bilinear terms to (a) substitute forced products (`lam=0` ⟹ product 0) and (b) feed tight bounds to the bit-blast width planner so the cascade sizes small. **Caveat:** this edges toward a theory capability; coordinate with the NIA lane to avoid duplicating z3's `nla`. Treat as exploratory, not the lane's load-bearing deliverable.

**Phase C (revised recovery targets):**
- QF_LIA `convert` 220 (all-sat) → **expect ≥ 30 recovery** (charter's original LIA target; now the lane's primary).
- SAT14 1635 → **reset expectation**: pure-preprocessing recovery likely small; real recovery is NIA-lane NLA work. Report honestly rather than chase.
- Soundness: 1958 oracle-blind wins preserved; full reg 0 unsound; pair-matrix over {SOLVE_EQS, REWRITE, PG_CNF, STRICT_VALIDATION}.

---

## 4. Soundness / methodology notes
- 0-disagreement is necessary but **blind to completeness** (sat/unsat→unknown regressions are invisible to the diff). Promotion gate = diff **AND** local unit+reg, never diff alone.
- Worktree built via `third_party` symlink to main (git blocks `file://` submodule clone; clone-from-superproject fails). Documented for the next agent.
