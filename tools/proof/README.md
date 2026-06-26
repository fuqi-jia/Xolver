# UNSAT proof tooling

The independent gate for Xolver's UNSAT proofs: Xolver emits a certificate, and a
**separate external checker** must accept it. This is the unsat-side analogue of
the `ArithModelValidator` sat-side gate. A proof a checker rejects is a release
blocker — exactly like an unsound verdict.

## Scripts

| Script | What it does |
|--------|--------------|
| `install_checkers.sh [dir]` | Build/install the external checkers: `drat-trim`+`lrat-check` (Boolean core) and `carcara` (Alethe, Phase C+). Self-tests that the gate is adversarially sound. |
| `check_proof.sh <xolver> <drat-trim> <file.smt2> [workdir]` | Solve one file with `--produce-proof`, then verify the emitted `<base>.cnf` + `<base>.drat` with `drat-trim`. Prints `VERIFIED` / `REJECTED` / `NO-PROOF` / `SKIP`. |
| `run_proof_corpus.sh <xolver> <drat-trim> <list>` | Run the gate over a corpus list (e.g. `docs/proof/corpus/UNSAT-CORPUS.txt`) and summarize. **Any REJECTED ⇒ exit non-zero (hard failure).** |

## Contract

- **`VERIFIED`** — Xolver emitted a proof and the independent checker accepted it.
- **`REJECTED`** — the checker refused a produced proof. **HARD FAILURE**; the
  corpus runner exits non-zero. A wrong proof is never acceptable.
- **`NO-PROOF` (degraded)** — Xolver answered `unsat` but produced no certificate
  (e.g. the refutation used theory lemmas not yet certified, or was decided in
  preprocessing). This is *allowed and honest*: we never emit a false proof to
  avoid the degraded path.
- **`SKIP`** — not `unsat`; nothing to certify.

## Phase status

- **Phase B (now):** the **propositional core**. A *complete* proof is produced
  only when the SAT core alone refutes (every clause went through `addClause`).
  When a theory lemma is fed via the external propagator, the captured DIMACS is
  incomplete, so Xolver suppresses the certificate (`NO-PROOF`) rather than emit
  one a checker would reject. Pure-Boolean unsats (e.g. pigeonhole) verify with
  `drat-trim`. All gated behind `-DXOLVER_ENABLE_PROOFS=ON` (default OFF).
- **Phase C+ (next):** capture/justify theory lemmas (EUF, LRA, …) as Alethe
  sub-proofs checked by `carcara`, turning the degraded theory instances into
  fully verified proofs.

## Quick start

```bash
# 1. build with proofs on
cmake -S . -B build -DXOLVER_ENABLE_PROOFS=ON && cmake --build build -j2
# 2. install the external checkers
bash tools/proof/install_checkers.sh
# 3. run the gate over the locked corpus
bash tools/proof/run_proof_corpus.sh build/bin/xolver \
     .proof-checkers/drat-trim/drat-trim docs/proof/corpus/UNSAT-CORPUS.txt
```
