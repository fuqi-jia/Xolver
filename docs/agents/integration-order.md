# Integration & Promotion Order (master-owned, living doc)

As-of 2026-05-26. The five agent branches are all **default-OFF for their flags** and
**not merged**. This doc is the master's plan for merging them into main soundly, in an
order that (1) lands soundness first, (2) minimizes shared-file merge pain, (3) re-runs the
double gate after each step. It's a living doc — update tips/status as rounds land.

## Branch state

| Branch | tip | Default-ON (soundness / behavior-neutral) | Flags (default-OFF) | In-flight (gates completion) |
|---|---|---|---|---|
| `agent/a1-linear` | 1b617da | bool-sort propagation fix (Solver.cpp ~458; recovers IDL 26 + LIA 3 → unsat, likely more across logics) | `ZOLVER_LRA_PIVOT_HEUR`, `ZOLVER_LIA_REPAIR` | IDL/RDL/LIRA flip recovery |
| `agent/a2-nonlinear` | 18bd5e0 | — | `ZOLVER_NIA_LOCALSEARCH`, `ZOLVER_NRA_VARORDER` | **NRA UNSAT-cert floor** + deep covering fix; NIA false-SAT extraction |
| `agent/a3-uf-arrays` | c657507 | O(1) symbolName reverse-index, builtin-eval skip (neutral) | `ZOLVER_UF_FAST_CC`, `ZOLVER_AX_ROW2_CONST` | **explainEquality mid-saturation fix** (DISEQ_WATCH withdrawn) |
| `agent/a4-combination-cdclt` | 83c1989 | `TheorySolver::setCareGraph` hook, `[TM-CHECK]` cerr gating | `ZOLVER_COMB_CAREGRAPH`, `ZOLVER_SAT_MIN`, `ZOLVER_SAT_LEMMA_MGMT`, `ZOLVER_COMB_MODEL_BASED` | **combination false-UNSAT floor** (only ungated unsound class) |
| `agent/a5-strategy-infra` | fa7c2cb | ArithModelValidator fixes (by-value maps, robust bool-detection) | `ZOLVER_PP_REWRITE`, `ZOLVER_STRAT_PRESETS`, `ZOLVER_PP_STRICT_VALIDATION` | validator-eval recovery (UFApply/array/algebraic) |

## Blockers before the integration is "sound-complete"

Soundness-first: these must land (on their branches, reviewed) before we cut the integrated
binary, because merging flag-OFF commits doesn't fix the underlying unsound defaults:

1. **A4 — combination false-UNSAT floor** (AUFLIA 1, UFNIA 2). This is the *one* unsound class
   with **no gate**: ModelValidator can't catch wrong UNSAT, A5's gate is sat→unknown only,
   A2's cert gate is NRA-only. Until A4 ships a fix or a combination UNSAT cert→Unknown floor,
   the merged binary is unsound on combined logics. **Highest blocker.**
2. **A2 — NRA UNSAT-cert floor** (positively-certifying; uncertified covering → Unknown). Closes
   the 16 NRA false-UNSAT.
3. **A3 — explainEquality mid-saturation fix** (the false-UNSAT that FAST_CC unmasks).
4. Recovery items (turn unknown/false → correct; not blockers for *soundness* but for *score*):
   A5 validator-eval, A1 IDL/RDL/LIRA flips, A2 NIA false-SAT extraction.

## Merge sequence (into an integration branch off main; whole-branch merges)

Chosen so the branch that owns each shared file's *foundational* change lands first, then others
layer their (different-method) edits on top. Re-run the double gate after **each** merge.

1. **A4 first.** It introduces the `TheorySolver::setCareGraph` base hook (TheorySolver.h) and
   edits EufSolver/LraSolver/LiaSolver to add the hook + prune. Landing it first means A3's and
   A1's later edits to those files merge on top of an existing hook. A4 also owns
   TheoryManager/sat/combination outright (no contention). Its flags are OFF; the `[TM-CHECK]`
   cerr gating is a clean neutral fix. **Precondition: blocker #1 (combination UNSAT floor) is in.**
2. **A5 second.** Owns Solver.cpp/frontend + ArithModelValidator. Lands its Solver.cpp blocks
   (~513 rewriter, ~866 presets, post-solve strict gate) and the unconditional validator fixes.
   At this merge, **decide whether to host A1's bool-sort fix inside `getOrCreateBoolSort`**
   (own the invariant for all call paths) vs. leaving A1's minimal Solver.cpp block.
3. **A1 third.** bool-sort fix (Solver.cpp ~458 — different region from A5's blocks, clean) +
   Lra/Lia flag features (different methods from A4's setCareGraph edits, clean). *Consider
   cherry-picking the bool-sort fix to land in step 0* if we want main sound on the IDL/LIA
   cluster before the full integration (it's foundational and may fix false-SAT across logics).
4. **A3 fourth.** EufSolver edits (canonicalization, UF perf, explainEquality fix, FAST_CC) merge
   on top of A4's setCareGraph EufSolver edits — different methods, additive. **Exclude the
   withdrawn DISEQ_WATCH** (ensure c657507's removal is what lands, not f04ea94's version).
5. **A2 last (order-flexible).** Most isolated (nia/nra own dirs); fewest conflicts. NRA cert
   floor + var-order + SLS + NIA extraction.

## Promotion gates (per flag → default-ON, master-enforced)

No flag flips to default-ON until BOTH hold (see README §Promotion-policy):
- its `unknown`-flips are recovered to only the genuinely-hard residual, AND
- a **panda A/B** vs z3 shows net gain + **0 new wrong/unsound on newly-reachable cases**.

Per-flag notes:
- **bool-sort fix (A1, unconditional):** already default-ON; needs a panda differential to confirm
  the global boolean-encoding shift only flips wrong→right (expected to fix false-SAT beyond IDL/LIA).
- **`PP_STRICT_VALIDATION` (A5):** promote only after A5 validator-eval + theory extraction recover
  the 77 (→ benchmark set) flips to the hard residual. Otherwise it inflates `unknown` ~12%.
- **`COMB_CAREGRAPH` (A4):** panda A/B must explicitly watch for NEW false-SAT in UFLRA/UFLIA/AUFLIA/
  UFNIA (validator can't catch combination false-SAT yet).
- **`UF_FAST_CC` (A3):** broad UF differential required (faster CC reaches new conflicts — see the
  explainEquality lesson), and only after the explainEquality fix lands.
- **`NRA_VARORDER` / `NIA_LOCALSEARCH` / `LIA_REPAIR` / `LRA_PIVOT_HEUR`:** recovery/heuristic aids,
  low risk; promote on a positive panda A/B (no unknown inflation expected).
- **`PP_REWRITE` (A5):** widen the soundness oracle to reals/UF/arrays + panda A/B before default-ON.
- **`STRAT_PRESETS` (A5):** the assembly seam — its `envFlags` arms get populated by the master as
  each underlying flag passes its own promotion gate (not before).

## After every merge
- Double gate: unit + 632 regression with flags OFF, 0 unsound (the merged default path).
- Spot differential vs z3 on the cases the merge's unconditional fixes touch.
- Never run regression during a concurrent agent build (WSL contention → spurious exit=-2).
