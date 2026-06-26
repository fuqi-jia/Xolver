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

- **`VERIFIED`** — a *complete* proof: every clause is in the formula and the
  checker accepted the refutation (0 theory lemmas assumed). A full propositional
  soundness certificate.
- **`VERIFIED-SKELETON (N lemmas assumed)`** — the checker accepted the refutation,
  but `N` theory lemmas were captured as **assumed axioms**. This certifies the
  **Boolean skeleton only** — the lemmas themselves are *not* yet justified (a
  wrong lemma would still pass here). The `.cnf`'s leading `c xolver-proof:`
  comment records the count. Phase C justifies each lemma (Alethe + Carcara) to
  upgrade these to full certificates. **Never read a skeleton as a full proof.**
- **`REJECTED`** — the checker refused a produced proof. **HARD FAILURE**; the
  corpus runner exits non-zero. A wrong proof is never acceptable. (With complete
  capture this should never happen; if it does, the capture missed a clause.)
- **`NO-PROOF` (degraded)** — Xolver answered `unsat` but produced no certificate
  (the refutation was decided outside the SAT core, e.g. in preprocessing). This
  is *allowed and honest*: we never fake a proof to avoid the degraded path.
- **`SKIP`** — not `unsat`; nothing to certify.

## Phase status

- **Phase B (done):** the **propositional core**. A custom CaDiCaL proof tracer
  (`ProofCnfCapture`) captures the *complete* input formula — original CNF plus
  every external-propagator clause (theory lemmas/conflicts/reason clauses), all
  recorded by CaDiCaL as input axioms — so `<base>.cnf` + `<base>.drat` are a
  self-contained refutation. Pure-Boolean unsats verify *complete*; theory
  instances verify their *Boolean skeleton* with the lemmas assumed. All gated
  behind `-DXOLVER_ENABLE_PROOFS=ON` (default OFF).
- **Phase C (in progress):** justify theory lemmas as Alethe sub-proofs checked
  by `carcara`, upgrading `VERIFIED-SKELETON` to full `VERIFIED`. **LRA Farkas
  landed**: an immediate simplex conflict over simple variable bounds on one
  variable (e.g. `x>0 ∧ x<0`) emits an `la_generic` proof with unit Farkas
  multipliers, plus an IR-derived `<base>.smt2`, checked `valid` by Carcara. The
  soundness guard restricts emission to the provably-correct case (positive,
  top-level, coeff-1, single-variable); everything else stays skeleton — **0
  rejected**. Next: row conflicts (real coefficients), EUF (`eq_transitive`),
  IDL/RDL (negative cycle).
  - Pass the Carcara binary as the 5th arg to `check_proof.sh` / 4th to
    `run_proof_corpus.sh` to check the Alethe proofs; without it, only the DRAT
    Boolean skeleton is checked.

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
