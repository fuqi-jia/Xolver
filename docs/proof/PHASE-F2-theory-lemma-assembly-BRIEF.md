# Phase F2 — theory-lemma Boolean assembly: clean-context implementation brief

Status: **design + de-risking done, not yet implemented.** Successor to F1
(`docs/proof/PHASE-F-general-boolean-assembly-BRIEF.md`, MERGED commit 765be76).
Read that + the `#15` section of `MEMORY → proof-implementation-state.md` first.

## What this closes
F1 emits one Carcara-verified Alethe proof for **pure-propositional** UNSAT (abstract:
build a fresh flat CNF over the ORIGINAL pre-purification assertions, LRAT-refute on a
dedicated CaDiCaL solve, clausify + replay the resolution). F2 extends that to **theory**
UNSAT whose refutation needs theory lemmas: `euf_039` (congruence), and the single-lemma
class generally. Each theory lemma becomes a derived clause whose `(cl ¬l1 .. ¬lk)`
tautology is **proven** by the existing single-conflict machinery (not assumed), spliced
into the resolution replay. Targets: `euf_039` first; then re-examine `euf_016` (may be
directly abstraction-unsat — no lemma) and `euf_061`/combination.

## The mechanism (reuses F1's plumbing)
1. **Theory-atom abstraction.** Each DISTINCT IR theory atom (`(= a b)`, `(= (f a)(f b))`,
   …) over the ORIGINAL assertions becomes one propositional variable. Render the atom via
   `dumpExprToSMT2` — so the abstraction's "variables" ARE the real atoms in the Alethe
   proof. (F1 already does this for Bool vars; F2 widens it to any theory atom.)
2. **Clausify the original assertions** over those atoms: `(and ...)` → `and :args(i)`;
   `(or ...)` → `or`; binary `(distinct x y)` → the unit `(not (= x y))`; n-ary
   `(distinct ...)` → its pairwise lowering (the IR's `NaryDistinctLowerer` form is an
   `(and (distinct ..) ..)` — clausify the And then each binary distinct); `(not ..)` and
   bare atoms → units. (All de-risked valid against Carcara.)
3. **Theory lemma clauses.** The refutation needs the theory tautology clauses
   `(cl ¬l1 .. ¬lk)` (e.g. congruence `(or ¬(= a b) (= (f a)(f b)))`). These come from the
   theory conflict cert(s) already in `proof::TheoryProofSink` (`pImpl->proofSink_`). The
   existing emit machinery (`buildConflictRefutation`, `EufCongruenceProver`, the
   la_generic verifier in `src/api/Solver.cpp`) ALREADY builds exactly this tautology
   clause — it is the `:rule eq_congruent/eq_transitive/la_generic` step BEFORE the final
   resolution-to-empty. **Refactor those builders to expose the lemma clause + its
   sub-proof steps**, instead of only the closed refutation.
4. **Refute + replay.** Build CNF = (clausified original clauses) ∪ (theory lemma clauses),
   feed to a dedicated CaDiCaL LRAT solve (the F1 `LratCapture` path), translate the LRAT
   chain to Alethe `resolution`. Each *original* clause id maps to its clausification
   step; each *theory-lemma* clause id maps to the lemma's tautology step (whose own
   sub-proof — congruence/transitivity/Farkas — is emitted just before it). End at `(cl)`.

## De-risked Alethe shape (Carcara `valid`, scratchpad /tmp/f2) — euf_039
Problem (IR-dumped): `(declare-fun f (U) U)`, a,b,c:U, `(assert (and (not (= (f a)(f b))) (not (= (f a)(f c))) (not (= (f b)(f c)))))`, `(assert (= a b))`.
```
(assume hAnd (and (not (= (f a)(f b))) (not (= (f a)(f c))) (not (= (f b)(f c)))))
(assume hEq (= a b))
(step t1 (cl (not (= (f a)(f b)))) :rule and :premises (hAnd) :args (0))   ; clausify original
(step t2 (cl (not (= a b)) (= (f a)(f b))) :rule eq_congruent)             ; theory lemma + its proof
(step t3 (cl) :rule resolution :premises (t1 t2 hEq))                      ; LRAT replay
```
All building blocks already validated: `and :args(i)`, `or`, `eq_congruent`/`eq_transitive`/
`la_generic`/`equiv1`/`refl`, order-insensitive/orientation-sensitive `resolution`.

## STAGING
**F2a — single-lemma theory cases.** When ONE theory conflict cert refutes the abstraction
(original clauses + that one tautology clause is propositionally unsat). `euf_039` is the
canonical target. No CEGAR. This is the first increment — ship it.
**F2b — multi-lemma / CEGAR.** When more than one lemma is needed: solve the abstraction
propositionally; on a SAT model, ask the theory solver for the violated lemma, add it,
repeat until unsat (bounded). Defer to a later increment.

## Blockers / pointers
- **B1 — expose lemma clause + sub-proof from the emit builders.** `src/api/Solver.cpp`:
  the la_generic / eq_transitive / congruence / bool_congruence branches currently build a
  CLOSED `AletheProof` ending in `(cl)`. Refactor so each can ALSO yield (a) the lemma
  clause literals `(cl ¬l1 .. ¬lk)` and (b) the `AletheProof` STEPS that derive it (the
  congruence/transitivity/Farkas steps), to be embedded in the larger proof. `AletheProof`
  (`src/proof/AletheProof.h`) `assume`/`step`/`serialize` compose; you likely build ONE
  `AletheProof` for the whole F2 proof and call into the per-lemma builders to append steps.
- **B2 — atom abstraction + clausify original.** Reuse F1's flat-clausal detection
  (`tryFlatClausalBooleanProof` in Solver.cpp) but over theory atoms. The IR atom <-> a
  CNF var id; render each atom via `dumpExprToSMT2`. Clausify And/Or/distinct/units. Watch
  the IR form of the original `(distinct ...)` (n-ary may already be lowered to pairwise
  binary by `NaryDistinctLowerer` — inspect `SolverImpl::originalAssertions_` for euf_039
  with a temporary gated `XOLVER_PROOF_DEBUG` dump; remove before commit).
- **B3 — lemma set = the captured conflict cert(s).** For F2a, take the single conflict
  from `proofUniqueConflict(pImpl->proofSink_.conflicts())` (already used by the single-
  conflict path). Its lits give the lemma `(cl ¬l1 .. ¬lk)`. Feed that clause + the
  clausified original to the LRAT solve. If propositionally unsat -> F2a applies; else it
  needs F2b (out of scope) -> degrade to skeleton.
- **B4 — splice in the LRAT replay.** Map each fed clause id (F1's feed-order map) to either
  a clausification step or a lemma tautology step; emit the lemma sub-proofs before the
  replay; translate the LRAT chain. Reuse `src/proof/BoolClausalProof.{h,cpp}` — extend
  `buildClausalRefutation` to accept, per input clause, EITHER an assume/clausify step id
  OR a pre-built lemma step id.
- Note: `euf_039`'s resolution is tiny; you MAY hand-build it without LRAT for F2a. But
  prefer reusing F1's LRAT path so F2 generalizes — confirm both give a Carcara-`valid`
  proof.

## Verification gates (ALL must pass before committing)
1. `euf_039` -> Carcara `valid`; `check_proof.sh` -> `VERIFIED (alethe/carcara)`.
2. Full proof corpus **0 REJECTED**, VERIFIED(complete) **>= 74** and RISES (euf_039, and any
   other single-lemma case, flip SKELETON->VERIFIED): `grep -rl ':status unsat' tests/regression/{bool,lra,euf,idl,rdl} | sort > /tmp/c.txt && bash tools/proof/run_proof_corpus.sh build/bin/xolver "$PWD/.proof-checkers/drat-trim/drat-trim" /tmp/c.txt "$PWD/.proof-checkers/carcara/bin/carcara"` -> `REJECTED=0`, exit 0.
3. Unit `./build/tests/xolver_unit_tests` -> SUCCESS (currently 1493).
4. Regression `python3 tools/regression/run_regression.py --root tests/regression --solver build/bin/xolver` -> **0 UNSOUND, 0 UNEXPECTED_FAIL** (lone `nra_200` TIMEOUT is a known flake).
5. `bash tools/governance/check_architecture.sh` -> satisfied (keep LRAT capture in `src/sat/` free of `theory/`/`frontend/` includes).
6. Behaviour-neutral: all new code `#ifdef XOLVER_ENABLE_PROOFS`; proofs-OFF byte-identical; DRAT/skeleton remains the fallback (degrade, never a wrong proof).

## Workspace / build / workflow
Worktree `/mnt/d/D_Work/ISCAS/projects/xolver-proof`, branch `proof/implementation` (at
765be76). Build `ulimit -v 4194304 && cmake --build build -j2` (keep `-j2`; run in
background, poll). Produce: `XOLVER_ENABLE_PROOFS=1 ./build/bin/xolver solve <f>.smt2
--produce-proof <base>`; check `./.proof-checkers/carcara/bin/carcara check <base>.alethe
<base>.smt2`. Commit only if ALL gates pass; `git push` to `proof/implementation` (do NOT
merge to main — the human ff-merges after CI `proof-gate` is green). If blocked, report the
precise obstacle and stop — no half-done code.
