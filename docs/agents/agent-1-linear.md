# Agent 1 — Linear Arithmetic Full Stack (LRA + LIA, incl. IDL/RDL)

You are one of five agents pushing **Zolver** (research C++ SMT solver, repo root
`/mnt/d/D_Study/BUAA/projects/NLColver`) toward SOTA. Read `docs/agents/README.md` for the
campaign overview, the **common contract** (soundness, flag-gating, double validation gate,
worktree, reporting), and **the method** — it applies to you in full. This is a **charter**,
not a one-shot task.

## Your bible (authoritative menus + minimal sets)

- `conversations/5.list/1.chatgpt.lra.md` — LRA: 80-item menu + ~40-item minimal set.
- `conversations/5.list/2.chatgpt.lia.md` — LIA: 100-item menu + 58-item minimal set.

Read both first. The minimal sets and the "必须做 / must-do" groupings define your priority
order. Key thesis from the files: **LRA SOTA gap is not "missing features" — it's CDCL(T)
integration, incremental backtracking, sparse exact computation, conflict-explanation
quality, pivot/propagation strategy.** And: **LIA ≠ naked branch-and-bound — it is LRA
relaxation + branch-and-cut + integer/congruence propagation + explanation-aware CDCL(T).**

## Step 1 — Audit (do this before writing code)

Map each minimal-set item to EXISTS-good / EXISTS-weak / MISSING with file:line evidence.
Orient with: `CLAUDE.md`, `src/theory/arith/README.md` (the `ArithSolverBase` + `Reasoner`
pipeline — **mandatory**), `plan.md` §5. Known starting points:
- LRA: `src/theory/arith/lra/` — `GeneralSimplex` (Dutertre–de Moura tableau, incremental).
  Check: is it sparse? revised/dual? watch-based bound propagation? Farkas explanation
  quality? basis restoration on backtrack? bound/explanation caches?
- LIA: `src/theory/arith/lia/LiaSolver.*` — branch-and-bound + disequality; tunable flags
  (`safeMode`, `ultraSafeMode`, `singleVar`, `gcdIneq`, `eqGcdNorm`). Check: any cutting
  planes? integer model repair? PB extraction? congruence/divisibility beyond GCD?
- Shared: `src/theory/arith/integer/IntegerReasoner.*` (GCD conflict/tightening),
  `src/theory/arith/linear/LinearConstraintNormalizer.*` (canonicalization),
  `src/theory/arith/presolve/PresolveEngine.cpp` (fixpoint — **wired only into NRA/NIA
  today, not LRA/LIA**), `src/theory/arith/{idl,rdl}/` (difference logic).
- Read z3/cvc5: `reference/z3/src/math/simplex/`, `reference/z3/src/smt/theory_arith*`,
  `reference/cvc5/src/theory/arith/linear/`.

## Step 2 — Highest-leverage gaps to fill (priority order, from the bibles)

Each behind a default-OFF `ZOLVER_LRA_*` / `ZOLVER_LIA_*` flag.

**LRA kernel + explanation (the SOTA dividing line):**
1. **Conflict-explanation quality** — Farkas-lemma explanation, **minimal conflict
   extraction**, theory-lemma generation, explanation cache. Short, stable, reusable
   conflicts/propagations to the SAT core. (`ZOLVER_LRA_FARKAS_MIN`)
2. **Watch-based bound propagation** + implied/fixed-variable detection + propagation queue
   — cut Simplex calls by propagating bounds early. (`ZOLVER_LRA_WATCH_PROP`)
3. **Backtrackable/incremental state** — trail-based restoration, **basis restoration**,
   sparse matrix update, bound cache (vs. rebuilding tableau on backjump).
4. **Sparse / dual / revised simplex** + stable pivot, degeneracy/cycling handling — if the
   current simplex is dense/primal-only. (`ZOLVER_LRA_DUAL_SIMPLEX`)
5. Exact rational arithmetic on the conflict/propagation/model path (internal fast repr OK,
   but conflicts/model must be exact) + model validation.

**LIA branch-and-cut + integer reasoning (the LRA→LIA leap):**
6. **Branch-and-cut**: Gomory, mixed-integer-rounding (MIR), Chvátal–Gomory, implied-bound
   cuts — *cut first, branch later, explanation-aware*. (`ZOLVER_LIA_CUTS`)
7. **Integer bound propagation + congruence/divisibility/modular + linear-congruence
   solving + Hermite normal form** — many LIA instances die here before any branching.
   (`ZOLVER_LIA_CONGRUENCE`) — note HNF/SNF already exists as presolve Cap 5; reuse it.
8. **LRA→LIA integrality repair** + SAT-guided integer search + integer model
   reconstruction — try rounding/repair before splitting. (`ZOLVER_LIA_REPAIR`)
9. **PB / finite-domain extraction** (pseudo-Boolean, cardinality, at-most-one,
   small-domain) + PB propagation — many LIA benchmarks are PB/scheduling in disguise.
   (`ZOLVER_LIA_PB`)
10. **Presolve into LRA/LIA**: wire `PresolveEngine` (today NRA/NIA-only) into LRA/LIA;
    add constraint subsumption/duplicate/tautology/trivial-conflict + linear variable
    elimination + difference-logic / unit-coefficient detection. (`ZOLVER_LIN_PRESOLVE`)

## Soundness notes specific to you
- A wrong Farkas/conflict clause or an over-eager cut produces unsound UNSAT that
  `ModelValidator` will **not** catch. Verify every conflict is genuinely entailed; every
  cut must be valid for all integer feasible points.
- Integer vs real: a real-sound substitution can be integer-unsound. Gate correctly.
- Eliminated variables must be reconstructable for the model (both LRA and LIA return
  models). Keep and apply the substitution map at model-build time.
- Epsilon/strict-inequality handling must stay exact (no doubles on the decision path).

## Setup & gate
Worktree per `docs/agents/README.md`, branch `agent/a1-linear`, id `a1`. Each technique
behind its `ZOLVER_*` flag, default OFF. Pass the **double gate** (flag OFF and ON: unit +
632-regression green, 0 unsound; focus your buckets: lra 57, lia 52, idl 15, rdl 12). Add
SMT2 regression cases. Report per the README (lead with your gap-analysis table). Do **not**
merge to main.
