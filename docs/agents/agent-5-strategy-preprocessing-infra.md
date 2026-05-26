# Agent 5 — Strategy/Portfolio + Preprocessing/Rewriter + Shared Infra

You are one of five agents pushing **Zolver** (research C++ SMT solver, repo root
`/mnt/d/D_Study/BUAA/projects/NLColver`) toward SOTA. Read `docs/agents/README.md` for the
campaign overview, the **common contract** (soundness, flag-gating, double validation gate,
worktree, reporting), and **the method** — it applies to you in full. This is a **charter**,
not a one-shot task.

## Your bible (the recurring system-level items in all six files)

Every theory file ends up demanding the same *system-level* capabilities. You own them:
- **Portfolio + strategy + variable/term ordering**: `3.chatgpt.nra.md` ("Portfolio NRA
  solving", "Learned Variable Ordering"), `4.chatgpt.nia.md` ("Portfolio NIA solving",
  "learning-guided branching", the "12 engineering combinations"), `2.chatgpt.lia.md`
  ("Portfolio LIA solving"). The files repeatedly say portfolio is *near-mandatory* for
  NRA/NIA.
- **Preprocessing / canonicalization / rewriting**: every file's "预处理" section —
  polynomial/term canonicalization, relation normalization, constant folding, hash-consing,
  DAG sharing, factorization (these last feed Agent 2 but the generic rewriter is yours),
  let-expansion, term-flattening, tautology/trivial-conflict elimination.
- **Caching / memory infra**: every "高级优化" section — arena allocation, object pooling,
  small-vector, hash-table control, generic cache scaffolding the theory agents reuse.
- **Model validation framework**: every file's "Model Validation" item — the soundness
  backstop the whole campaign relies on.

Theses: a SOTA solver wins on **rich preprocessing + good strategy selection**, and the
formula rewriter is currently a stub — your single biggest gap. Portfolio turns the theory
agents' flags into measured wins per instance class.

## Step 1 — Audit (before writing code)

Map the system-level minimal-set items to EXISTS-good / EXISTS-weak / MISSING with file:line
evidence. Orient with: `CLAUDE.md` (dispatch section + invariants 1, 2, 6), `plan.md` §2, §11.
Known starting points:
- **Rewriter — essentially a stub**: `src/expr/rewriter.cpp:16` (`installZolverRewriteRules`
  is empty; only SOMTParser defaults run; no fixpoint, no memoized Zolver rule set). Invoked
  at `src/parser/adapter.cpp:21`. Rule API: `r.rules().onGT(...)`.
- Frontend preprocessing pipeline: `src/api/Solver.cpp` (ITE lowering ~521, constant
  propagation ~544, div/mod lowering ~588, to_int lowering ~683; `originalAssertions_`
  snapshot ~512 feeds `ModelValidator` — **do not break it**). `src/frontend/preprocess/`,
  `src/frontend/atomization/Atomizer.cpp` (plain Tseitin + memo; no polarity-awareness/gate
  detection).
- Strategy/dispatch: `src/frontend/factory/TheoryFactory.cpp` (`setupSolvers`, hardcoded
  per-logic switch; LIA flags threaded here), `src/theory/core/LogicFeatureDetector.*`
  (formula feature scan). **No portfolio, no stage timeouts, no strategy scheduling, no
  anytime behavior.**
- Infra: `src/util/` (`SmallVector`, IDs). Check arena/pool/cache scaffolding.
- Read z3/cvc5: `reference/cvc5/src/smt/set_defaults.cpp` (strategy-by-logic),
  `reference/cvc5/src/preprocessing/`, `reference/z3/src/ast/rewriter/`,
  `reference/z3/src/ast/simplifiers/`, `reference/z3/src/tactic/` (strategy/portfolio ideas).

## Step 2 — Highest-leverage gaps to fill (priority order)

Each behind a default-OFF `ZOLVER_STRAT_*` / `ZOLVER_PP_*` flag.

1. **Real memoized, fixpoint formula rewriter** (the #1 gap): boolean identities/absorption/
   const-fold, arithmetic flatten+normalize+collect, relational canonicalization
   (`p ⋈ q → p−q ⋈ 0`). DAG-safe + memoized (invariant 6). Populate
   `installZolverRewriteRules` or add a `CoreIr`-level rewrite pass in `frontend/preprocess/`.
   (`ZOLVER_PP_REWRITE`)
2. **Per-logic strategy presets** — a strategy table keyed by logic + cheap
   `LogicFeatureDetector` features, selecting solver knobs (LIA flags, NRA var-order,
   candidate budgets, CaDiCaL config) and **which of the other agents' flags to enable**.
   This is the backbone the whole campaign plugs into. (`ZOLVER_STRAT_PRESETS`)
3. **Portfolio scheduler with stage timeouts + anytime** — sequential portfolio: run config
   A to a soft deadline (`CadicalBackend::requestTerminate`), on unknown/timeout reset and
   try config B (flip safe-mode, var-order, presolve flags, escalate effort). Always return
   the best **sound** verdict; timeouts produce `unknown`, never a wrong answer.
   (`ZOLVER_STRAT_PORTFOLIO`)
4. **Learned / dynamic variable & term ordering** plumbing shared across theories (NRA/NIA
   need it most; coordinate with Agent 2). (`ZOLVER_STRAT_LEARNED_ORDER`)
5. **CNF/Tseitin improvements**: polarity-aware (Plaisted-Greenbaum) + gate/shared-subexpr
   detection in the Atomizer. (`ZOLVER_PP_PG_CNF`)
6. **Generic caching / memory infra**: arena allocation, object pooling, hash-cons/DAG-share
   utilities, cache scaffolding the theory agents reuse. (`ZOLVER_PP_INFRA` where runtime-
   visible; pure infra can land enabled if provably behavior-neutral + regression-green.)
7. **Model-validation framework hardening** + cone-of-influence / unused-assertion pruning.
   (`ZOLVER_PP_COI`)

## Soundness notes specific to you
- A wrong rewrite rule is instant unsoundness `ModelValidator` will NOT catch if it yields a
  wrong UNSAT. Unit-test each rule against a brute-force/random-model oracle.
- **Portfolio/timeouts may only ever produce `unknown`, never a wrong sat/unsat.** Any
  verdict a config returns still passes `ModelValidator` (SAT) / rests on a sound proof
  (UNSAT). Never let a heuristic config short-circuit validation (invariants 1 & 2).
- Polarity-aware CNF is sound only if polarity is tracked correctly through `not`/`ite`
  (both polarities)/`=`/`xor` (mixed) — fall back to full Tseitin when unsure.
- Don't disturb the `originalAssertions_` snapshot / ModelValidator contract.

## Setup & gate
Worktree per `docs/agents/README.md`, branch `agent/a5-strategy-infra`, id `a5`. Each
technique behind its `ZOLVER_*` flag, default OFF (except provably behavior-neutral infra).
Pass the **double gate** (flag OFF and ON: unit + 632-regression green, 0 unsound — your
changes are global, so watch *all* buckets). You will edit shared `Solver.cpp` /
`TheoryFactory.cpp` heavily — keep changes additive + flag-gated and document every shared-
file edit for the master (Agent 1/2 touch presolve, Agent 4 touches TheoryManager/sat).
Report per the README (lead with gap-analysis). Do **not** merge to main.
