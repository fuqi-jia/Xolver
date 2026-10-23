# UNSAT proof tooling

External checkers validate emitted proof artifacts. Build with
`-DXOLVER_ENABLE_PROOFS=ON` to enable proof export. This option controls evidence
production; a solver verdict alone does not imply a complete certificate.

| Script | Interface |
| --- | --- |
| `install_checkers.sh [dir]` | Install pinned drat-trim, lrat-check and Carcara; run checker self-tests |
| `check_proof.sh <xolver> <drat-trim> <input.smt2> [workdir] [carcara]` | Check every query's exported artifacts and verdict sequence |
| `run_proof_corpus.sh <xolver> <drat-trim> <list> [carcara]` | Run the checker over a list and report coverage |

| Result | Meaning |
| --- | --- |
| `VERIFIED` | Checker accepts the emitted CNF without assumed theory lemmas, or Carcara accepts an Alethe proof against the emitted SMT problem |
| `VERIFIED-SKELETON` | DRAT refutation is valid for a Boolean abstraction containing assumed theory lemmas; those lemmas are not certified |
| `REJECTED` | Produced evidence is invalid or a verdict contradicts the input status; validation fails |
| `NO-PROOF` | UNSAT has no exported certificate; counted separately from verified evidence |
| `SKIP` | Query is SAT or UNKNOWN |
| `ERROR` | Solver execution, query manifest or checker setup failed; validation fails |

Alethe proofs are checked against the exported problem. Input translation and
normalization remain trusted unless independently justified. A checked artifact
therefore does not establish an end-to-end proof of the original source formula
or of the C++ implementation. The distinction applies to complete emitted CNF
proofs as well as theory proofs.

Multi-query files have separate input snapshots and artifacts per query. Any
rejection or execution error fails the corpus run. Missing evidence remains a
coverage gap even when other queries produce valid proofs.

```bash
cmake -S . -B build -DXOLVER_ENABLE_PROOFS=ON
cmake --build build -j2
bash tools/proof/install_checkers.sh
bash tools/proof/run_proof_corpus.sh build/bin/xolver \
  .proof-checkers/drat-trim/drat-trim docs/proof/corpus/UNSAT-CORPUS.txt \
  .proof-checkers/carcara/bin/carcara
```

CI checks Boolean and selected arithmetic/EUF certificates. Quantifier and SL
solving have separate evidence capabilities; unsupported proof export is not
reported as successful verification.
