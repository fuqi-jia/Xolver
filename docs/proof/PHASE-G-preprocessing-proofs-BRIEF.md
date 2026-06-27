# Phase G (#16) — preprocessing / frontend proofs: scoping + first-increment brief

Status: **scoping + initial de-risking done; this is the LARGEST and most
architecturally invasive remaining piece — treat as a multi-increment research-adjacent
subsystem, not a single agent run.** Read `MEMORY → proof-implementation-state.md`
(#16 + the trusted-boundary notes) first.

## The gap (precise)
Every proof in the pipeline today is checked by Carcara against the **IR-derived**
problem (`dumpProblemToSMT2(IR)`), NOT the original SMT-LIB. The step
`original SMT → (SOMTParser parse-time folds + ~19 CoreIR preprocessing passes) → IR`
is **TRUSTED** — assumed correct, unproven. On the SAT side this is mitigated by
`ModelValidator` re-checking every `sat` against the ORIGINAL; on the UNSAT side there is
**no** equivalent re-derivation. A buggy preprocessing pass could turn a sat problem into
an unsat-looking IR and the proof would still "verify" (against the wrong problem). #16
closes this: emit Alethe **rewrite steps** proving `original-assertion ≡ IR-assertion`
per transformation, so the proof checks against the **ORIGINAL** formula.

This subsumes `euf_002/045` (`(distinct a a)` folded to `false` in SOMTParser's
`mkDistinct`/`mkOper`, before CoreIR — confirmed) and is the only path to a fully
end-to-end-trusted UNSAT certificate.

## The architecture change
1. Dump the **ORIGINAL** assertions as the problem `.smt2` (a new dumper over
   `SolverImpl::originalAssertions_` / the parser AST, NOT the post-preprocess IR).
2. For each asserted formula, emit Alethe steps deriving its IR/normalized form from the
   original via rewrite rules; then the existing core proof (LRA/EUF/Boolean assembly)
   runs over the normalized atoms.
3. The proof's top-level `assume`s become the ORIGINAL assertions; everything the core
   proof currently `assume`s (IR atoms) must instead be DERIVED by a rewrite chain.

## What is de-risked (Carcara 1.1.0)
- Carcara **parses original formulas** including a literal `(distinct a a)` (probed with a
  `hole` step → `holey`).
- The **`*_simplify` rewrite family EXISTS**: `eq_simplify`, `and_simplify`, `or_simplify`,
  `bool_simplify` are known rules (probes returned "expected <args>", i.e. known rule /
  malformed args — the exact arg form must be worked out per rule from the Alethe spec
  `docs/proof/refs/alethe-spec.pdf`). `connective_def` exists. **`all_simplify` and
  `distinct_simplify` are NOT in this Carcara** — some folds (e.g. `(distinct a a)→false`)
  need composition (binary distinct → `(not (= ))` then `eq_simplify`/`refl`) rather than a
  single rule.
- Orientation/symmetry of equalities is already absorbed by `eq_transitive`/`eq_congruent`
  in the core proofs, so canonicalization flips do NOT each need a `symm` step inside the
  core — but they WILL matter at the original↔IR boundary.

## The per-pass landscape (each needs a rewrite proof; ~19 CoreIR passes + parser folds)
`NaryDistinctLowerer` (n-ary distinct → pairwise And), `UnconditionalConstantPropagation`
(identity folds `(= a a)→true`, `(distinct a a)→false`, value folds), `FormulaRewriter`,
`ArithCastNormalizer`, `IntDivModLowerer`/`IntDivModConstantFold`, `RealDivLowerer`,
`ToIntDefinitionalLowerer`, `ToRealLiteralFold`, `BoolSubtermPurifier`,
`UfInArithPurifier`, `SolveEqs`, `UnconstrainedElim`, ITE removal, plus the SOMTParser
parse-time folds (`mkDistinct`/`mkOper`/`mkAnd`/…). Each maps to one or a few Alethe
rewrite rules. This is why #16 is the largest piece — it is a per-transformation
rewrite-proof layer, exactly what cvc5/veriT implement as their "preprocessing proof".

## Recommended MINIMAL first increment (G1)
Do NOT attempt the whole pipeline. Pick the ONE simplest, most self-contained
transformation and prove it end-to-end against the original:
- **Candidate: the identity self-distinct fold** `(distinct a a) → false` (euf_002/045).
  G1 proof shape (to be worked out + de-risked against Carcara BEFORE coding): problem
  asserts the original `(distinct a a)`; proof `assume`s it, rewrites binary distinct to
  `(not (= a a))` (definitional / `connective_def`?), `refl` gives `(= a a)`, resolution →
  `(cl)`. REQUIRES intercepting the fold so the original assertion survives to the proof
  layer with a recorded justification — but the fold is in SOMTParser (parse time), so G1
  likely needs the original assertion recovered from the parser AST, not the folded IR.
- **Alternative G1: a CoreIR-level fold** (`UnconditionalConstantPropagation` identity
  fold) where the original assertion IS available pre-fold in `originalAssertions_` and the
  transformation is one rule — easier to intercept than the parser fold.
Gate G1: one such case flips from NO-PROOF/skeleton to `VERIFIED (alethe/carcara)` checked
against the ORIGINAL formula, 0 REJECTED, all other gates hold.

## Blockers
- **B1 — recover the original assertions + a per-assertion rewrite trace.** Preprocessing
  passes currently transform in place without recording a justification. You need each pass
  (and the parser) to emit a structured `(original_subterm, rule, rewritten_subterm)` trace
  under `XOLVER_ENABLE_PROOFS`. This is the bulk of the work and touches the whole frontend.
- **B2 — original-formula dumper.** A new `dumpProblemToSMT2`-analogue over the original
  assertions (parser AST or a pre-preprocess IR snapshot), sort-consistent (reuse
  `inferConstCtx`).
- **B3 — rewrite-rule mapping.** Per transformation, the exact Alethe rule + arg form
  (from the spec). Some need composition (no single rule). Validate EACH against Carcara
  before wiring (the de-risking discipline that made F1/F2/the EUF increments land clean).
- **B4 — splice the rewrite chain ABOVE the core proof.** The core proof currently assumes
  IR atoms; rebuild so it assumes original assertions, applies the rewrite chain to reach
  the IR atoms, then runs the existing core steps. Reuse `AletheProof`.

## Honest assessment / recommendation
This is research-adjacent and the largest of the remaining tasks. Unlike F1/F2 (which had a
single de-risked end-to-end shape and landed in one clean agent run), #16 is a broad
per-pass effort with an architecture change (proof target IR→original) and a frontend-wide
trace requirement (B1). **Recommended:** do G1 (one fold, end-to-end, against the original)
as a proof-of-concept FIRST — de-risk its exact Alethe shape against Carcara, intercept the
single transformation, and prove that one case against the original. Only widen to more
passes once G1 demonstrates the architecture. Expect multiple increments. The SAT-side
`ModelValidator` already covers the sat direction, so #16's marginal soundness value is the
unsat-side preprocessing trust — real, but weigh it against the breadth of B1.

## Gates (every increment) + workspace
Same 6 gates as F1/F2 (target Carcara-valid AND now checked against the ORIGINAL formula;
corpus 0 REJECTED, VERIFIED ≥ current; unit; reg 0-unsound; arch; proofs-OFF byte-identical).
Worktree `/mnt/d/D_Work/ISCAS/projects/xolver-proof`, branch `proof/implementation`; build
`ulimit -v 4194304 && cmake --build build -j2`; checkers under `./.proof-checkers/`. Commit
only if ALL gates pass; push to branch; human ff-merges after CI `proof-gate` green. No
half-done code.
