# Agent 3 — EUF + Arrays Full Stack (QF_UF + QF_AX)

You are one of five agents pushing **Zolver** (research C++ SMT solver, repo root
`/mnt/d/D_Study/BUAA/projects/NLColver`) toward SOTA. Read `docs/agents/README.md` for the
campaign overview, the **common contract** (soundness, flag-gating, double validation gate,
worktree, reporting), and **the method** — it applies to you in full. This is a **charter**,
not a one-shot task.

## Your bible (authoritative menus + minimal sets)

- `conversations/5.list/5.chatgpt.uf.md` — QF_UF: core / preprocessing / CDCL(T) / advanced
  / engineering-combos minimal sets.
- `conversations/5.list/6.chatgpt.ax.md` — QF_AX: core / rewrites / preprocessing / EUF-combo
  / model / CDCL(T) / advanced minimal sets. **The largest, most detailed file.**

Read both first. Key theses: **QF_UF SOTA = incremental E-graph + backtrackable union-find +
rollback signature table + parent/use-list congruence propagation + disequality watch +
explanation forest + lazy theory propagation + congruence-closed model — the dividing line is
explanation *quality* (short, cached, backjump-compatible) and rollback speed, not "can it
do closure."** And: **QF_AX should be a *lazy* array solver built on the EUF engine: select/
store rewriting + store-chain normalization + weak-equivalence graph + lazy extensionality +
diff witness + finite-map model construction — NOT eager axiom saturation, NOT
Ackermannization-first, NOT quantifier instantiation.**

## Step 1 — Audit (before writing code)

Map each minimal-set item to EXISTS-good / EXISTS-weak / MISSING with file:line evidence.
Orient with: `CLAUDE.md` (dispatch + invariants), `plan.md` §6. Known starting points:
- EUF: `src/theory/euf/` — `IncrementalEGraph`, `RollbackUnionFind`, `RollbackSignatureTable`,
  `ProofForest` (explanations), `EufTermManager`, `EufSolver`. The core list in the UF bible
  is largely present — your job is mostly the *quality/advanced/cache* tier. Check:
  explanation minimization/compression? watch-based disequality? lazy theory propagation
  budgeting? the cache layer (signature/merge/explanation/representative)? dirty-class
  queues? deterministic representative selection?
- Arrays: `src/theory/array/ArrayReasoner.*` — currently **eager Row1/ConstArray, lazy
  Row2/Ext** axiom lemmas (dedup via `row2Done_`/`extDone_`), layered on the EUF e-graph
  (`EufSolver::enableArrays`). **Check for the big gap: is there a weak-equivalence graph at
  all, or is it axiom-instantiation only?** Diff-witness function? store-chain normalization?
  finite-map array model construction? array-specific explanations?
- Read z3/cvc5: `reference/cvc5/src/theory/uf/` (`equality_engine`, care-graph),
  `reference/cvc5/src/theory/arrays/` (`theory_arrays.cpp` — weak-equivalence, RIntro),
  `reference/z3/src/smt/theory_array*`, and the weak-equivalence papers the AX bible cites.

## Step 2 — Highest-leverage gaps to fill (priority order, from the bibles)

Each behind a default-OFF `ZOLVER_UF_*` / `ZOLVER_AX_*` flag.

**EUF (quality + advanced tier, since the core exists):**
1. **Explanation minimization + compression + explanation cache** — shorter EUF conflict/
   propagation reasons help the whole CDCL(T) loop. (`ZOLVER_UF_EXPLAIN_MIN`)
2. **Watch-based disequality checking** + class-pair disequality watch + lazy theory
   propagation budgeting — find disequality conflicts immediately, cheaply.
   (`ZOLVER_UF_DISEQ_WATCH`)
3. **Cache/representation tier**: signature/merge/representative/term-to-class caches,
   dirty-class & dirty-application queues, rebuild-on-demand, arena/object-pool/small-vector.
   (`ZOLVER_UF_CACHES`)
4. **Deterministic** representative selection + merge ordering (reproducibility + stable
   explanations). (`ZOLVER_UF_DETERMINISTIC`)

**Arrays (the high-value reorg toward the modern lazy approach):**
5. **Weak-equivalence graph** + weak congruence closure — the modern lazy alternative to
   read-over-write/extensionality saturation the bible centers on. Likely the single biggest
   array win. (`ZOLVER_AX_WEAKEQ`)
6. **Diff-function reasoning + array difference witness** for disequalities + **lazy
   extensionality** scheduling (when/how-short to emit ext lemmas, backjump-compatible,
   cached). (`ZOLVER_AX_DIFF_WITNESS`)
7. **Select/store rewriting + store-chain normalization** (select-over-store same/diff index,
   store-over-store, idempotence, shadowing, constant-array) as a preprocessing layer.
   (`ZOLVER_AX_REWRITE`)
8. **Finite-map array model construction** + completion + default value + model validation
   (select-store / extensionality / functional-consistency). Soundness-critical: arrays had
   prior bugs. (`ZOLVER_AX_MODEL`)
9. **CDCL(T) array integration quality**: lazy lemma scheduling + lemma/propagation budgeting
   + lemma/explanation/conflict caches; avoid repeated read-over-write splitting.
   (`ZOLVER_AX_LAZY_SCHED`)

## Soundness notes specific to you
- Arrays are soundness-sensitive (prior Row2/Ext bugs). Read-over-write + extensionality must
  stay **complete** for the logic — a missing extensionality witness in final-check = wrong
  SAT (caught by ModelValidator) but a wrong lemma = wrong UNSAT (not caught). Add a
  differential check vs z3 on array cases.
- Weak-equivalence is only sound if the graph faithfully captures all store paths; under-
  approximating loses models. Build conservative, verify against the eager axioms on tests.
- EUF explanation minimization must keep the reason a valid entailment (still explains the
  merge/conflict). Disequality watch must never miss a real conflict.

## Setup & gate
Worktree per `docs/agents/README.md`, branch `agent/a3-uf-arrays`, id `a3`. Each technique
behind its `ZOLVER_*` flag, default OFF. Pass the **double gate** (flag OFF and ON: unit +
632-regression green, 0 unsound; focus your buckets: euf 62, ax 10, and the array-combination
logics alia/alra/auflia/auflra which depend on your array core). Add SMT2 regression cases.
Report per the README (lead with gap-analysis). Do **not** merge to main.
