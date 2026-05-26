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

1. **Combination false-UNSAT** — split after diagnosis:
   - **UFNIA ×2: FLOORED** by A4 `ZOLVER_SAT_DEFER_EARLY_CONFLICT` (`4caa248`, sound→unknown,
     intent default-ON). Correctness recovery = **A3 explainEquality** (A4 traced the 168-lit
     conflict to the combination interface = the explainEquality bug). A4 re-tests after A3 lands.
   - **AUFLIA `fb_var_27_8`: STILL UNGATED → A5.** 0 theory checks = boolean-abstraction/atomization
     false-UNSAT; A4's floor can't gate it (no theory conflict), A1's bool-sort fix doesn't fix it.
     A5 soundness-priority. **Remaining highest blocker.**
2. **A2 — NRA UNSAT-cert floor** (positively-certifying; uncertified covering → Unknown). Closes
   the 16 NRA false-UNSAT. Interim conservative floor acceptable; precise verifier recovers later.
3. **A3 — explainEquality / N-O proof-forest rewrite** — root-caused (unsound BFS explanations);
   the **shared soundness lever**: fixes A3 DISEQ_WATCH + FAST_CC promotion + A4 UFNIA correctness.
4. Recovery items (unknown/false → correct; for *score*, gated by the promotion rule):
   A5 validator-eval (UFApply done; arrays/algebraic next), A1 IDL/RDL flips (done), A2 NIA
   false-SAT extraction + 20 algebraic-model flips.

### Cross-agent producing→consuming handoffs (this round)
- **Combination shared-scalar model** (the `i→"@e6"` token-loss false-flip): A5 `dd7a24a` *consumes*
  the typed `numericAssignments` channel; **A1 must POPULATE it from LIA** (cleaner) and/or **A4 fix
  `TheoryManager::getModel` first-wins aggregation** so a shared scalar's arith value beats the EUF
  token. Then A5's ~5 array/combination flips auto-recover.
- **`ite_nested_sat` (QF_UF, correct verdict / wrong printed model) → A5**: default model builder must
  populate pure-bool var values from the SAT assignment (the capture A5 wrote for the strict path).
- Re-bucketed strict-validation flips out of A1: `ite_nested_sat→A5`, `uflra_001→A3/A4`, `lira_009→A2`
  (A1 residual now 0). A5 maintains the live flip doc on its branch; this table is authoritative.

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
