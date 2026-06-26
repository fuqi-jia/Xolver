# Locked UNSAT proof corpus (Phase A)

This is the **reference set** against which every later phase of the unsat-proof
pipeline is checked. It is intentionally **small** so an external checker can run
over the whole set in seconds, yet **broad** so every supported logic lane is
represented.

- **`UNSAT-CORPUS.txt`** — the locked list (46 files, 2 per logic lane).
- **`select_corpus.sh`** — the reproducible selector that generated it.

## Selection criteria

1. The file declares `(set-info :status unsat)`.
2. It is **not** tagged `:xolver-expected known-fail` / `known-unsound`
   (we only owe a proof for unsats the solver is expected to decide).
3. The **2 smallest** files (by line count) per `tests/regression/<logic>/`
   directory — small instances external-check fast and are trivial to debug when
   a rule is wrong.

Regenerate with:

```bash
bash docs/proof/corpus/select_corpus.sh > docs/proof/corpus/UNSAT-CORPUS.txt
```

## Lane → phase mapping

The corpus spans all 23 regression logic directories. Phases consume it
incrementally (see `../PROOF-IMPLEMENTATION-PLAN.md`):

| Phase | Theories exercised | Corpus dirs |
|-------|--------------------|-------------|
| B (Boolean core) | propositional skeleton for **all** | every file |
| C.1 | EUF, LRA | `euf/`, `lra/` |
| C.2 | LIA, IDL, RDL | `lia/`, `idl/`, `rdl/` |
| C.3 | arrays, datatypes | `ax/`, `alia/`, `alra/`, `ania/`, `dt/` |
| C.4 | NRA, NIA, mixed | `nra/`, `nia/`, `nira/`, `lira/` |
| E (combination) | Nelson–Oppen glue | `uflia/`, `uflra/`, `auflia/`, `auflra/`, `aufnia/`, `ufnia/`, `ufnra/`, `ufdtnia/` |

## Notes

- This corpus is the **proof-checking** reference, distinct from the full
  regression gate (808 files) which still runs in its entirety every phase.
- A file may move/rename across regression refactors; regenerate the list and
  re-commit if `select_corpus.sh` output changes.
