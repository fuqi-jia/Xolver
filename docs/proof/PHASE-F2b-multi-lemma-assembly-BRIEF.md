# Phase F2b — multi-lemma Boolean assembly: clean-context implementation brief

Status: **design + de-risking done, not yet implemented.** Successor to F2a
(`docs/proof/PHASE-F2-theory-lemma-assembly-BRIEF.md`, MERGED commit 0a9be1e). Read it +
F1 + the `#15`/F2a section of `MEMORY → proof-implementation-state.md` first.

## What this closes
F2a emits one Carcara-verified Alethe proof when a **single** theory lemma refutes the
propositional abstraction (`euf_039`). F2b extends to **multiple** theory lemmas. Targets,
empirically (via `check_proof.sh`):
- `euf_016` (`(distinct a b c)` + `(= a c)`), `euf_015` (`(= a b c)` + `(distinct a c)`):
  **"1 lemma assumed"** — single-lemma cases F2a MISSED (warm-ups; see B1 below).
- `euf_061_unsat_n_distinct_pigeon`: **"27 lemmas assumed"** — the real multi-lemma target.
- combination-logic interface conflicts (overlaps #11).

## Reuse + the new piece
F2a already does: theory-atom abstraction over `originalAssertions_`, clausify the original
(`and`/`or`/`distinct_elim`/units), one lemma clause from a captured conflict, LRAT refute
on a dedicated CaDiCaL solve, replay via `proof::appendLratResolutionReplay`, each lemma's
tautology sub-proof spliced (`EufCongruenceProver` `lemmaMode`). F2b's new piece: **gather
the FULL lemma set** (not one), feed all lemma clauses + the clausified original to the LRAT
solve, and splice each lemma's sub-proof. The multi-lemma Alethe shape is just F2a's shape
with N lemma steps + a larger resolution — all building blocks already Carcara-valid.

## Two ways to source the lemma set (investigate + pick; recommend A first)
**A — collect ALL captured conflicts (no CEGAR; preferred).** The main CDCL(T) solve already
generated every theory lemma it needed; the theory side pushes conflicts to
`proof::TheoryProofSink` (`pImpl->proofSink_.conflicts()`). F2a took the UNIQUE one
(`proofUniqueConflict`); F2b takes ALL of them, each → a lemma clause + its sub-proof.
INVESTIGATE FIRST (gated `XOLVER_PROOF_DEBUG` dump, removed before commit): for `euf_061`,
how many distinct conflicts does `proofSink_.conflicts()` hold, and are their lits over
atoms recoverable from `originalAssertions_`? If the captured set makes
(clausified-original ∪ lemma-clauses) propositionally UNSAT (check on the dedicated LRAT
solve), A is complete — ship it. NOTE: propagation/instantiation lemmas may NOT all reach
the sink (only conflicts via `pushEufTransitivityCert`/`pushLraFarkasCert`/`pushBool
CongruenceCert`/etc.) — if the set is insufficient, fall to B.
**B — CEGAR (fallback, if A is incomplete).** Solve the abstraction propositionally; on a
SAT model, map it to a theory-atom assignment, invoke the theory solver to produce a
conflict lemma for that assignment, add it, repeat until propositionally unsat (bounded).
This guarantees a complete, cert-carrying lemma set but is a NEW harness (controlled
theory-solver invocation for proof production) — heavier; only do it if A cannot complete.

## Blockers / pointers
- **B1 — why F2a missed the single-lemma euf_016/015 (do this FIRST, it is diagnostic).**
  F2a's emit fires when `proofUniqueConflict` returns a cert AND the closed-proof path did
  not emit. For `euf_016`/`euf_015` either (a) the sink holds 0 or ≥2 conflicts (so
  `proofUniqueConflict` returns null), or (b) the abstraction+1-lemma is not propositionally
  unsat as F2a builds it (atom-identity mismatch: the `(= a c)` inside `(distinct a b c)`
  vs the standalone `(= a c)` must be the SAME abstraction var — they ARE hash-consed in the
  IR; confirm the clausifier keys atoms by ExprId, not by rendered string). Fixing this may
  already flip euf_016 and is the natural first F2b step. (euf_015's lemma needs the n-ary
  `Eq` `(= a b c)` — Carcara has NO clean n-ary-eq decomposition rule; it may stay skeleton
  or need a composed rewrite — keep it out of scope if it resists.)
- **B2 — collect all conflicts + dedup.** Replace the `proofUniqueConflict` gate in the F2a
  emit path with "collect all distinct conflicts" (reuse the `same`/dedup logic from
  `proofUniqueConflict`). Each conflict → one lemma clause (its tautology) + sub-proof
  (`EufCongruenceProver` lemmaMode, the la_generic verifier, bool_congruence — all already
  expose lemma steps after F2a's refactor).
- **B3 — feed all lemma clauses to the LRAT refute + map ids in the replay.** Extend
  `tryTheoryLemmaBooleanProof` (Solver.cpp) to add N lemma clauses; `appendLratResolution
  Replay` already maps each fed input clause id to its pre-built Alethe step — just pass the
  N lemma steps alongside the clausification steps.
- **B4 — atom abstraction coverage.** All conflict-lit atoms AND all clausified-original
  atoms must share one ExprId→propvar map. Atoms only in lemmas but not in the original
  clauses still need a propvar (they appear in the resolution). Render via `dumpExprToSMT2`.

## De-risked
Every building block is already Carcara-valid and merged: `and :args`/`or`/`distinct_elim`/
`equiv1`/`eq_congruent`/`eq_transitive`/`la_generic`/`refl`, order-insensitive
orientation-sensitive `resolution`, and F1/F2a's LRAT capture + `appendLratResolution
Replay`. A multi-lemma proof is structurally N single-lemma splices sharing one resolution —
no new rule. (If you want a 2-lemma sanity proof, hand-build one in /tmp and Carcara-check
before wiring — same discipline as every prior increment.)

## Verification gates (ALL must pass before committing)
1. `euf_016` (and ideally `euf_061`) → Carcara `valid`; `check_proof.sh` → `VERIFIED
   (alethe/carcara)`.
2. Full proof corpus **0 REJECTED**, VERIFIED(complete) **>= 75 and RISES**:
   `grep -rl ':status unsat' tests/regression/{bool,lra,euf,idl,rdl} | sort > /tmp/c.txt &&
   bash tools/proof/run_proof_corpus.sh build/bin/xolver "$PWD/.proof-checkers/drat-trim/drat-trim" /tmp/c.txt "$PWD/.proof-checkers/carcara/bin/carcara"` → `REJECTED=0`, exit 0.
3. Unit `./build/tests/xolver_unit_tests` → SUCCESS (1493).
4. Regression `python3 tools/regression/run_regression.py --root tests/regression --solver build/bin/xolver` → **0 UNSOUND, 0 UNEXPECTED_FAIL** (lone `nra_200` TIMEOUT is a known flake).
5. `bash tools/governance/check_architecture.sh` → satisfied (src/sat/ clean of theory/frontend).
6. Behaviour-neutral: all new code `#ifdef XOLVER_ENABLE_PROOFS`; proofs-OFF byte-identical; DRAT/skeleton stays the fallback (degrade, never a wrong proof).

## Workspace / workflow
Worktree `/mnt/d/D_Work/ISCAS/projects/xolver-proof`, branch `proof/implementation` (at
6330c2d). Build `ulimit -v 4194304 && cmake --build build -j2` (run in background, poll).
Produce `XOLVER_ENABLE_PROOFS=1 ./build/bin/xolver solve <f>.smt2 --produce-proof <base>`;
check `./.proof-checkers/carcara/bin/carcara check <base>.alethe <base>.smt2`. Commit only if
ALL gates pass; push to branch; human ff-merges after CI `proof-gate` green. If blocked
(e.g. captured-lemma set insufficient → would need full CEGAR), report precisely and stop —
no half-done code. It is FINE for this increment to flip euf_016 (+ whatever else the
captured-conflict set covers) and leave euf_061/combination to a later CEGAR increment if A
proves insufficient — report which cases flipped and why.
