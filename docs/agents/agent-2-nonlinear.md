# Agent 2 — Nonlinear Arithmetic Full Stack (NRA + NIA, incl. NIRA/LIRA)

You are one of five agents pushing **Zolver** (research C++ SMT solver, repo root
`/mnt/d/D_Study/BUAA/projects/NLColver`) toward SOTA. Read `docs/agents/README.md` for the
campaign overview, the **common contract** (soundness, flag-gating, double validation gate,
worktree, reporting), and **the method** — it applies to you in full. This is a **charter**,
not a one-shot task.

## Your bible (authoritative menus + minimal sets)

- `conversations/5.list/3.chatgpt.nra.md` — NRA: core-algorithm minimal set (23) +
  preprocessing minimal set (43).
- `conversations/5.list/4.chatgpt.nia.md` — NIA: core (40) + linearization (24) +
  preprocessing (large) + the "12 engineering combinations to select all."

Read both first. Key theses: **NRA SOTA = CDCAC/NLSAT conflict-driven kernel + ICP/
linearization fast filter + Lazard/root/sign/algebraic-number kernel + reason minimization
(set-cover) + learned variable ordering + portfolio + strong polynomial preprocessing/cache
— NOT full classical CAD.** And: **NIA is undecidable — there is no single complete path;
it needs a portfolio: bounded bit-blasting (find SAT), incremental linearization / LIA
relaxation (the backbone), modular/congruence/divisibility (catch integer UNSAT), CP/
finite-domain propagation (prune), local search (find SAT fast), NRA relaxation + integer
repair (fallback), conflict-driven portfolio scheduling.**

## Step 1 — Audit (before writing code)

Map each minimal-set item to EXISTS-good / EXISTS-weak / MISSING with file:line evidence.
Orient with: `CLAUDE.md` (esp. invariant 7 NIA-soundness, invariant 1 candidate-validation),
`src/theory/arith/README.md` (**mandatory**), `plan.md` §8–§12. Known starting points:
- NRA: `src/theory/arith/nra/` — CDCAC engine + presolve fixpoint;
  `nra/preprocess/{GcdEngine,SquarefreeEngine,SubresultantEngine,PolynomialNormalizer}`;
  Lazard projection WIP (`nra/projection/`, `nra/LAZARD.md`); `nra/engine/ReasonMinimizer`
  (`minimizeL0/L1/L2`). Check: NLSAT/model-based projection? conflict generalization?
  set-cover reason minimization? learned variable ordering? projection/root/sign caches?
- NIA: `src/theory/arith/nia/NiaSolver.*` — 16-stage `Reasoner` pipeline (RRT univariate,
  algebraic/GCD/modular, bounded enumeration, presolve, **bit-blast** stage `nia.bit-blast`,
  local-search stage). Check: is incremental linearization a real main path? is local search
  real (SLS) or a stub? NRA-relaxation + integer repair? CP/finite-domain propagation?
  portfolio scheduling across these?
- Shared: `linearizer/IncrementalLinearizer` (McCormick + secant/tangent/nonneg square
  cuts), `icp/IcpEngineZ` + `contractors/`, `interval/`, `bit_blast/`, `poly/LibPolyKernel`
  (gate libpoly behind `#ifdef ZOLVER_HAS_LIBPOLY`), `search/CandidateModelSearch`.
- Read z3/cvc5: `reference/z3/src/nlsat/`, `reference/z3/src/math/polynomial/`,
  `reference/cvc5/src/theory/arith/nl/` (`cad/`, `icp/`, `nl_model`).

## Step 2 — Highest-leverage gaps to fill (priority order, from the bibles)

Each behind a default-OFF `ZOLVER_NRA_*` / `ZOLVER_NIA_*` flag.

**NRA:**
1. **Reason minimization + conflict generalization** (set-cover-with-reasons, per the 2026
   CDCAC paper the bible cites) — smaller learned conflict clauses are the documented
   bottleneck. Extend `ReasonMinimizer`. (`ZOLVER_NRA_SETCOVER_MIN`)
2. **Fast-filter layer before CDCAC**: ICP contraction + linearization (McCormick/tangent/
   secant/RLT) + LRA relaxation to discharge candidates without full CAD.
   (`ZOLVER_NRA_FILTER`)
3. **Learned / dynamic variable ordering** (CAD is extremely order-sensitive) + portfolio
   over orderings. (`ZOLVER_NRA_VARORDER`)
4. **Algebraic-kernel caches**: projection cache, root-isolation cache, sign-evaluation
   cache, polynomial DAG sharing — NRA cost is repeated algebra. (`ZOLVER_NRA_CACHE`)
5. **Polynomial preprocessing**: canonicalization, factorization, squarefree, primitive
   part, equality substitution/reduction-mod-equalities, structure detection (univariate/
   quadratic/monomial → route to the cheap sub-solver). (`ZOLVER_NRA_PREPROC`)

**NIA (portfolio is near-mandatory here):**
6. **Incremental linearization as a real main path** (abstraction-refinement: nonlinear
   term → aux var → LIA relaxation → refinement lemma when model violates semantics).
   (`ZOLVER_NIA_INCR_LIN`)
7. **Local search / SLS** for fast SAT on bounded integer models. (`ZOLVER_NIA_LOCALSEARCH`)
8. **NRA relaxation + integrality repair** as fallback; **CP/finite-domain propagation +
   integer ICP** for pruning. (`ZOLVER_NIA_NRA_REPAIR`, `ZOLVER_NIA_CP_PROP`)
9. **Modular/congruence/divisibility/parity cuts** for integer UNSAT;
   bounded **bit-blasting** for small-domain SAT (tune the existing stage).
   (`ZOLVER_NIA_MODULAR_CUTS`)
10. **Portfolio scheduler** selecting among {bit-blast, linearization, CP, local-search,
    complete fallback} by formula features — coordinate with Agent 5's portfolio framework.
    (`ZOLVER_NIA_PORTFOLIO`)

## Soundness notes specific to you
- **NIA: never emit UNSAT from incomplete reasoning** (invariant 7). Bit-blast/linearization/
  local-search results are *candidates* validated by the exact kernel (invariant 1) — never
  let a shortcut bypass validation.
- Every factorization must pass `exactDivide` (GcdEngine already insists — keep it). Factor
  sign-splitting must enumerate ALL sign cases or you lose models.
- ICP/linearization derived UNSAT must be reason-tracked (ReasonedBox) and sound.
- Reason minimization must keep the conflict a valid theory lemma (still entailed).

## Setup & gate
Worktree per `docs/agents/README.md`, branch `agent/a2-nonlinear`, id `a2`. Each technique
behind its `ZOLVER_*` flag, default OFF. Pass the **double gate** (flag OFF and ON: unit +
632-regression green, 0 unsound; focus your buckets: nra 139, nia 109, nira 30, lira 37).
Add SMT2 regression cases. If you edit shared `PresolveEngine.cpp`, keep it minimal and flag
it (Agent 1 edits it too). Report per the README (lead with gap-analysis). Do **not** merge
to main.
