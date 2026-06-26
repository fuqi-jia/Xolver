# Plan: machine-checkable UNSAT proofs for Xolver (research → full implementation)

## Mission

Turn Xolver's proof *scaffold* into a real pipeline that, for every `unsat` it
reports, can **emit a machine-checkable proof certificate** that an **independent
external checker accepts**. This is the unsat-side analogue of the `ModelValidator`
soundness gate that already guards every `sat`.

Scope is unsat proofs (proof production + checking). The sat-side `ModelValidator`
is done and out of scope except as a design template.

## Non-negotiable gate (inherits CLAUDE.md)

Soundness over completeness. Every phase must end green on:
```
cd build && cmake --build . -j2 && ctest && \
python3 tools/regression/run_regression.py --root tests/regression --solver build/bin/xolver
```
with **0 `UNSOUND`** rows. Proof phases add a second, equally hard gate:

> **An unsat that emits an *unverifiable* proof is a release blocker — same
> severity as an unsound verdict.** If a real proof cannot be produced for an
> `unsat`, the solver may emit `unsat` *without* a proof (degraded), but must
> **never** emit a proof an external checker rejects. No wrong proofs, ever.

Proof logging is gated behind `XOLVER_ENABLE_PROOFS` (build option) /
`XOLVER_ENABLE_PROOFS=1`, **default OFF**; the no-proof decision path must not
regress (verify decided-count delta = 0 with proofs off).

## Existing state — the scaffold to build on (audit confirmed)

| File | What it is today | What it must become |
|------|------------------|---------------------|
| `src/proof/ProofManager.{h,cpp}` | records theory lemmas as **strings**; `exportAlethe()`/`exportLFSC()` are **skeletons**; `setSatProofFile()` exists | real structured proof terms + a complete Alethe assembler |
| `include/xolver/Proof.h` | **stub** (`isEmpty()→true`) | the public `Proof` value type (`toAlethe()`, `save()`, …) |
| `app/main.cpp` `proof-check` | prints `(stub)` | invoke an external checker (or a built-in) and return verified/failed |
| `src/proof/ModelValidator.{h,cpp}` | **done** — sat-side soundness gate | design template only (narrow, value-typed, soundness floor) |
| flag `XOLVER_ENABLE_PROOFS` | exists | gates the whole proof path (default OFF) |

Theory conflicts/lemmas are generated inside each theory solver
(`src/theory/arith/logics/*`, `src/theory/euf/`, `src/theory/array/`,
`src/theory/combination/`) and reach the core via the lemma/conflict path — that
is where structured justifications must be captured (Phase C).

## Phases

Each phase = its own commit(s), each ending on the gate above.

### Phase A — Research, audit, format decision (read-only; the "download references" step)
- **Audit** end-to-end: where every theory emits a conflict/lemma and what
  justification data is in hand at that point (LRA Farkas multipliers, EUF
  congruence/merge chains, NRA CAD cell certificates, array Row/ext instances,
  NIA cuts/branches); how CaDiCaL is configured and whether it can emit DRAT/LRAT;
  how `ProofManager` is fed today.
- **Research + download references** into `docs/proof/refs/`:
  - **Alethe** format spec + **Carcara** checker (the leading Alethe checker).
  - **DRAT-trim** / **LRAT** (`lrat-check`) for the propositional core.
  - **LFSC** (alternative; the scaffold already names it).
  - Published proof-rule algorithms only — **NO z3/cvc5 source** (algorithmic
    attribution is fine; copying code/symbol names is forbidden, per CLAUDE.md).
  - Theory-certificate literature: Farkas/Simplex, EUF congruence closure proofs,
    Lazard/CAD certificates, cut/branch proofs for integers.
- **Decide** the target: recommended default is **Alethe (theory + CDCL(T) glue)
  with LRAT for the Boolean core**, checked by **Carcara + lrat-check**. Justify
  in writing; this decision drives B–E.
- **Deliverable:** `docs/proof/RESEARCH.md` — format decision, reference index,
  per-theory proof-rule mapping table, and a gap analysis (which theories have
  clean certificates now vs. need new bookkeeping).
- **Gate:** no solver change → trivially green. Lock a small **unsat corpus**
  (subset of `tests/regression/**` with `:status unsat`, spread across logics) as
  the proof-checking reference set for all later phases.

### Phase B — Propositional core proof (Boolean skeleton)
- Configure CaDiCaL to emit DRAT/LRAT; thread it through
  `ProofManager::setSatProofFile`. Establish that the **Boolean** reasoning —
  given the theory lemmas as input clauses — checks with `lrat-check`/`drat-trim`.
- **Deliverable:** every instance in the unsat corpus produces a propositional
  proof that the external SAT-proof checker accepts (theory lemmas treated as
  assumed axioms at this phase).
- **Gate:** regression 0-unsound; SAT-proof checks 100% on the corpus.

### Phase C — Theory lemma certificates (the hard core, one theory at a time)
- Replace the string `justification` with **structured, checkable** proof terms.
  Sequence **easiest-first**, each landing independently:
  1. **EUF** (congruence/transitivity chains) and **LRA** (Farkas combination) —
     clean, well-specified certificates.
  2. **LIA/IDL/RDL** (cuts, branch, Bellman–Ford negative cycle).
  3. **Arrays / datatypes** (Row, extensionality, selector instances).
  4. **NRA / NIA** — hardest (CAD/Lazard cell certificates, NLA cuts). If a sound,
     checkable certificate isn't tractable, route that lemma to **degraded
     "no-proof"** mode (Phase-gate floor) rather than emit an unsound rule.
- **Deliverable:** for each migrated theory, its emitted lemmas produce Alethe
  sub-proofs that **Carcara accepts** on that theory's unsat corpus.
- **Gate:** per-theory external check passes; regression 0-unsound; proofs-off
  decided-count delta = 0.

### Phase D — Assembly + checker integration + public API
- `ProofManager::exportAlethe()` assembles the **complete** proof: theory
  sub-proofs (C) glued to the Boolean resolution (B) into one CDCL(T) Alethe proof.
- Implement the `proof-check` CLI for real: shell out to **Carcara** (and/or
  `lrat-check`) and report verified/failed with a non-zero exit on failure.
- Make `Proof` (`include/xolver/Proof.h`) a real value type
  (`Solver::getProof()`, `Proof::toAlethe()`, `Proof::save(path)`); the umbrella
  header already exports it.
- **Deliverable:** end-to-end — `xolver solve --produce-proof X.smt2` →
  `xolver proof-check` → **external checker verifies** — on the full unsat corpus.
- **Gate:** end-to-end external verification 100% on the corpus; 0-unsound.

### Phase E — Coverage, combination, CI, hardening
- Cover **Nelson–Oppen combination** proof steps (purifier/interface-equality
  justifications, `src/theory/combination/`) and any remaining theories.
- Enforce the **soundness floor** in code: an unsat whose proof fails to
  externally check is a hard error in the proof CI lane (never a silent pass).
- Add a **CI lane** (mirror `.github/workflows/ci.yml`) that, with
  `XOLVER_ENABLE_PROOFS=ON`, produces and **externally checks** proofs over the
  corpus; red on any unverifiable proof.
- Add an arch rule in `tools/governance/check_architecture.sh` if a new boundary
  appears (e.g. proof emitters must not leak into `src/expr/`).
- **Gate:** proof corpus 100% externally verified; full regression 0-unsound;
  `bash tools/governance/check_architecture.sh` green.

## Verification (end-to-end)

1. **Per phase:** build + `ctest` + `run_regression.py` → 0 `UNSOUND`.
2. **Behaviour-neutrality (proofs OFF):** decided-count delta vs. the pre-work
   binary = 0 — adding proof *logging* must not change any verdict or search path.
3. **Proof validity (proofs ON):** an **independent external checker**
   (Carcara / `lrat-check`) accepts **every** proof produced over the unsat
   corpus. Count of unverifiable proofs must be **0**.
4. **Degraded honesty:** instances where no proof is produced still answer
   `unsat` and are *logged as no-proof*; they never emit a rejected proof.

## Risks

- **A wrong proof rule is an unsoundness-class bug** → external-check gate on
  every phase; never trust a self-emitted proof without external confirmation.
- **NRA/NIA certificates are research-hard** → sequence easy theories first; gate
  hard ones behind degraded no-proof mode rather than risk an unsound rule.
- **CaDiCaL ↔ theory-lemma alignment** → the propositional proof's input clauses
  must exactly match the theory lemmas fed to the SAT core; verify in Phase B.
- **Performance / scope** → all proof bookkeeping behind `XOLVER_ENABLE_PROOFS`
  (default OFF); never regress the competition (no-proof) path.
- **Provenance** → published algorithms only; no z3/cvc5 source or symbol names.

## First concrete step

Create an isolated worktree, then execute **Phase A**: audit the conflict/lemma
paths + `ProofManager`, download references into `docs/proof/refs/`, and write
`docs/proof/RESEARCH.md` with the format decision and per-theory mapping. Zero
solver change; it is the shared input to every later phase.
