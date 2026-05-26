# Agent 4 — Theory Combination + CDCL(T) Integration

You are one of five agents pushing **Zolver** (research C++ SMT solver, repo root
`/mnt/d/D_Study/BUAA/projects/NLColver`) toward SOTA. Read `docs/agents/README.md` for the
campaign overview, the **common contract** (soundness, flag-gating, double validation gate,
worktree, reporting), and **the method** — it applies to you in full. This is a **charter**,
not a one-shot task.

## Your bible (cross-cutting sections of all six files)

You own the recurring cross-cutting machinery that *every* theory file demands. Read these
sections specifically:
- `5.chatgpt.uf.md` → "CDCL(T) 集成" + "Nelson-Oppen" sections (equality sharing, demand-driven
  arrangement, interface equalities, reason→clause, backjump-compatible explanation).
- `6.chatgpt.ax.md` → "AX / EUF 组合" + "CDCL(T) 集成" sections (array equality sharing,
  Nelson-Oppen array combination, lazy lemma scheduling, lemma/propagation budgeting).
- `1.chatgpt.lra.md` / `2.chatgpt.lia.md` → "CDCL(T)/theory combination 接口" (theory
  combination interface, Nelson-Oppen equality propagation).
- `3.chatgpt.nra.md` / `4.chatgpt.nia.md` → conflict-driven integration + reason handling.

Theses: **SOTA combined-logic performance lives in the combination layer and the theory↔SAT
interface, not in any single theory.** The dividing items are: care-graph / demand-driven
arrangement (so interface equalities don't explode), model-based combination, equality
sharing both directions, short backjump-compatible reason clauses, theory-lemma DB
management, and propagation/conflict budgeting. UF/LRA are convex → equality sharing
suffices; LIA/NIA are non-convex → need correct arrangement handling.

## Step 1 — Audit (before writing code)

Map the cross-cutting minimal-set items to EXISTS-good / EXISTS-weak / MISSING with file:line
evidence. Orient with: `CLAUDE.md` ("Solver dispatch and theory combination" + invariants
1 & 2), `plan.md` §5–§6. Known starting points:
- Combination: `src/theory/combination/` — `Purifier` (decomposes mixed assertions into pure
  atoms + bridge defs + shared-equality atoms), `SharedTermRegistry` (shared terms/owners,
  numeric-const dedup), `SharedEqualityManager` (interface (dis)equalities, per-level
  rollback), `ExplainableRollbackUnionFind`. **Check: is there any care-graph / care-function?
  Are interface equalities guessed broadly (combinatorial) or demand-driven? Model-based
  combination?**
- CDCL(T) driver: `src/theory/core/TheoryManager.*` (`check(lemmaStorage, effort)`, two
  effort levels; `combinationMode`/`nonConvexMode`/`arrayCombinationMode` flags;
  arrangement-splitting), `src/theory/core/TheoryLemmaDatabase.*` (**dedup only — no
  relevance/age/deletion policy**).
- SAT interface: `src/sat/CadicalBackend.*` (CaDiCaL wrapper, `configure`, assumptions,
  `requestTerminate`), `src/sat/CadicalTheoryPropagator.*` (IPASIR-UP callbacks; theory
  propagation; `MAX_MODEL_CHECKS` cap). Check reason→clause conversion, backjump
  compatibility, propagation/conflict budgeting.
- Theory-agnostic conflict minimization exists **only** in NRA (`nra/engine/ReasonMinimizer`)
  — generalize it.
- Read z3/cvc5: `reference/cvc5/src/theory/combination_care_graph.cpp`,
  `reference/cvc5/src/theory/theory_engine.cpp`, `reference/cvc5/src/theory/uf/` (care graph),
  `reference/z3/src/smt/smt_context.cpp` (relevancy, theory propagation).

## Step 2 — Highest-leverage gaps to fill (priority order)

Each behind a default-OFF `ZOLVER_COMB_*` / `ZOLVER_SAT_*` flag.

1. **Care-graph / care-function + demand-driven arrangement** — each theory reports only the
   shared-term pairs it actually cares about; split interface equalities on that small set
   instead of all pairs. Typically the biggest combined-logic speedup (QF_UFLRA/UFLIA,
   QF_ALIA/ALRA/AUFLIA/AUFLRA, UFNIA/UFNRA). (`ZOLVER_COMB_CAREGRAPH`)
2. **Model-based theory combination** — derive candidate shared (dis)equalities from the
   current partial model, propagate, split only on genuine disagreements. Must stay sound for
   the non-convex case (LIA/NIA disequalities). (`ZOLVER_COMB_MODEL_BASED`)
3. **Equality sharing both directions** + cross-theory explanation + combination conflict/
   lemma generation + delayed equality sharing. (`ZOLVER_COMB_EQ_SHARE`)
4. **Theory-agnostic conflict/lemma minimization** — lift NRA's `ReasonMinimizer` to LRA/LIA/
   EUF/array conflicts; shorter learned clauses → better propagation. (`ZOLVER_SAT_MIN`)
5. **Theory-lemma DB management** — relevance/activity/age + deletion policy for the *theory*
   lemma layer (don't touch CaDiCaL's own clause DB). (`ZOLVER_SAT_LEMMA_MGMT`)
6. **Propagation / conflict / lemma budgeting** + cheap-vs-full effort tuning + lazy lemma
   scheduling — control when expensive theory work runs. (`ZOLVER_SAT_BUDGET`)
7. **Reason→clause + backjump-compatible explanation** hardening across all theories +
   explanation/lemma/conflict caches at the combination layer. (`ZOLVER_COMB_EXPLAIN_CACHE`)

## Soundness notes specific to you
- Care-graph under-approximation loses completeness (→ wrong SAT, caught) but a buggy care
  set or arrangement can yield **wrong UNSAT** (not caught). Default conservative; expand the
  care/arrangement set when unsure; verify against the broad-guess path on tests.
- Non-convex theories (LIA/NIA) need correct arrangement/disequality handling — never assume
  convexity.
- Lemma deletion must not drop a lemma the current proof depends on; prune only the cache and
  re-derive on demand. Conflict minimization must keep the clause entailed.
- Everything still flows through `ModelValidator` (SAT) and sound UNSAT proofs (invariants
  1 & 2). Heuristic propagation never writes solver state directly.

## Setup & gate
Worktree per `docs/agents/README.md`, branch `agent/a4-combination-cdclt`, id `a4`. Each
technique behind its `ZOLVER_*` flag, default OFF. Pass the **double gate** (flag OFF and ON:
unit + 632-regression green, 0 unsound; focus the combined buckets: uflra/uflia/ufnia/ufnra +
the array-combination logics + euf). You will edit shared `TheoryManager`/`sat`/`combination`
heavily — keep changes additive + flag-gated, and document every shared-file edit for the
master (theory agents touch their explanation interfaces too). Report per the README (lead
with gap-analysis). Do **not** merge to main.
