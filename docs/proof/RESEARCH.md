# Phase A — Research, audit, and format decision for machine-checkable UNSAT proofs

**Status:** Phase A deliverable (read-only research; zero solver change).
**Companion files:** `PROOF-IMPLEMENTATION-PLAN.md` (the plan), `refs/INDEX.md`
(reference index + pinned versions), `corpus/` (locked unsat reference set).

This document records (1) the **format decision** and its justification, (2) the
**end-to-end audit** of where every theory emits a conflict/lemma and what
justification data is in hand, (3) the **per-theory proof-rule mapping**, and
(4) a **gap analysis** ranking theories by how ready their certificates are.

---

## 0. TL;DR

- **Target format: Alethe**, checked by the independent **Carcara** checker, with
  the **Boolean core emitted as DRAT/LRAT** by the vendored CaDiCaL (rel-3.0.0,
  native `DratTracer`/`LratTracer`) and checked by the **adversarially-sound
  `drat-trim`** (with `cake_lpr`, the CakeML-*verified* LRAT checker, as the
  hardened floor in Phase E). This is the plan's recommendation, now *confirmed
  against the actual code*: CaDiCaL can emit DRAT/LRAT today, and Alethe has
  first-class rules for every Xolver theory (`la_generic` carries Farkas
  coefficients; `eq_congruent`/`eq_transitive` for EUF; resolution for the core).
- **Checker soundness was verified, not assumed** (§1.4): `drat-trim` correctly
  *rejects* a bogus empty-clause proof of a SAT formula; the `lrat-check` in the
  drat-trim repo trusts solver hints and rubber-stamps such a claim, so it is
  **not** the gate on its own. Carcara 1.1.0 is installed and runs.
- **The proof is two-layer, by necessity.** Theory lemmas enter the CaDiCaL proof
  as *input clauses* ("after the query line"), **not** as propositionally-derived
  steps. So the LRAT proof certifies the Boolean skeleton *only relative to* the
  theory lemmas; each lemma needs its **own theory sub-proof**. This is the
  standard CDCL(T) proof-stitching obligation and it dictates the B→C→D sequence.
- **The whole scaffold is greenfield.** `ProofManager`, `Proof`, `proof-check`,
  and `--produce-proofs` are stubs called from *nowhere* outside unit tests. The
  one real asset is the **sat-side soundness gate** — and the live one is
  `ArithModelValidator` (exact, producer-independent, 3-valued), **not** the
  boolean-only `src/proof/ModelValidator` (test-only skeleton). Mirror the former.
- **Readiness ranking (easiest→hardest to certify):** EUF ≈ IDL/RDL (both
  *available now*) → LRA → Combination glue → LIA → Datatype → NIA-algebraic →
  Array → NIA-bitblast/Omega/NIRA-LIRA → NRA. EUF already contains a
  proof-producing congruence forest and IDL/RDL holds the negative cycle at
  emission; NRA/NIA cell certificates are research-hard and start in **degraded
  no-proof** mode.
- **One correctness bug to fix early:** `XOLVER_ENABLE_PROOFS` defaults **ON** and
  is read by **no** `#ifdef` — it gates nothing. Phase B flips it to default-OFF
  and makes it actually gate the proof path (the plan requires default-OFF).

---

## 1. Format decision

### 1.1 Decision

> **Emit Alethe for the theory + CDCL(T) glue, with LRAT for the Boolean core.
> Check with Carcara (Alethe) and lrat-check (LRAT). Keep LFSC as a documented
> fallback only.**

### 1.2 Why Alethe (over LFSC, DRAT-only, or a bespoke format)

| Criterion | Alethe + Carcara | LFSC + lfscc | DRAT/LRAT only | bespoke |
|-----------|------------------|--------------|----------------|---------|
| Independent checker, push-button | **Yes (Carcara, Rust, maintained)** | yes (older) | yes (SAT only) | no (we'd write+trust it) |
| SMT-LIB-native syntax (Xolver already prints it) | **Yes** | no (LF terms) | n/a | — |
| First-class theory rules (LRA Farkas, EUF cong) | **Yes** (`la_generic`, `eq_congruent`) | via signatures | **No** (propositional only) | — |
| Covers the *theory* obligation, not just Boolean | **Yes** | yes | **No** | — |
| Escape hatch for unsupported steps | `hole` rule | side-conditions | — | — |
| Soundness independence (separate authors/tool) | **strong** | strong | strong | **weak** |

- **DRAT/LRAT alone is insufficient** — it only certifies the *propositional*
  refutation. It cannot express *why a theory lemma is T-valid* (a Farkas
  combination, a congruence chain). It is necessary (the Boolean core) but not
  sufficient; hence Alethe on top.
- **A bespoke checker is rejected on principle** — the soundness floor requires an
  *independent* checker (the unsat analogue of `ArithModelValidator` being a
  separate evaluator). A checker we write and trust ourselves provides no
  independent confirmation.
- **LFSC is viable but higher-friction** — the scaffold names `exportLFSC()`, but
  Carcara is push-button, Rust, SMT-LIB-native, and actively maintained. LFSC is
  kept as a fallback for any single rule that proves intractable in Alethe.
- **Alethe was built for exactly this shape**: its spec states the rules are
  "structured around resolution and the introduction of theory lemmas, in the
  same way as CDCL(T)-based SMT solvers" (Alethe spec §Foreword) — i.e. our
  architecture.

### 1.3 The two-layer architecture (and its trust boundary)

```
   original SMT formula  ──frontend/atomizer──▶  CNF (Boolean abstraction)
            │                                          │
            │  (theory solvers emit lemmas/conflicts)  │
            ▼                                          ▼
   theory lemma clauses  ───────────────────▶  CaDiCaL SAT core
            │                                          │
            │ each lemma: Alethe theory sub-proof      │ LRAT proof of
            │ (la_generic / eq_congruent / …)          │ "CNF ∪ lemmas ⊢ ⊥"
            ▼                                          ▼
        Carcara  ◀──────── assembled Alethe ────────  lrat-check
```

The certificate is sound iff **all three** hold:
1. **(LRAT, Phase B)** the clause set `CNF ∪ {theory lemmas}` is propositionally
   UNSAT — checked by lrat-check on CaDiCaL's LRAT.
2. **(Alethe theory sub-proofs, Phase C)** every clause used as input that is a
   *theory lemma* (not original CNF) is T-valid — checked by Carcara.
3. **(Encoding faithfulness, trusted/Phase D-E)** the original CNF clauses
   faithfully encode the original SMT formula (the atomizer/Tseitin step). Alethe
   expresses this with the clausification rules (`and_pos`, `or_pos`, …); making
   it explicit removes it from the trusted base.

Phase D decides whether to ship this as **two artifacts** (`.lrat` + `.alethe`
glued by a thin linker that confirms the LRAT's non-CNF input clauses are exactly
the Alethe-proved lemmas) or to **translate the LRAT resolution chain into Alethe
`resolution` steps** for a single Carcara-checked artifact. LRAT's antecedent
hints make that translation mechanical; the choice is a tractability call made in
Phase D, not now.

### 1.4 Checker soundness — verified empirically, not assumed

A proof checker is a soundness gate **only if it rejects invalid proofs**. We
tested this adversarially before committing to a checker (reproducible via
`refs/checker-soundness-test.sh`):

| Checker | valid UNSAT proof | bogus empty-clause proof of a **SAT** formula | verdict |
|---------|-------------------|-----------------------------------------------|---------|
| **`drat-trim`** (full forward RUP) | verifies (exit 0) | **rejects** — `conflict claimed, but not detected` (exit 1) | **adversarially sound → use as the Boolean-core gate** |
| `lrat-check` (drat-trim repo) | verifies | **accepts** (rubber-stamps) | trusts solver hints; **not** a gate against a *wrong* proof |
| `cake_lpr` (CakeML-verified) | verifies | rejects (machine-checked soundness) | **the hardened floor (Phase E)** |

- Root cause for `lrat-check`: for an empty clause `list[0]=0` the pivot is
  degenerate, `RATs==0`, and `start==0`, so it returns `SUCCESS` unless a listed
  hint clause *independently* conflicts (`lrat-check.c` `checkClause` lines
  154/160-164). Genuine solver hints do conflict, so it is fine for real output —
  but it cannot catch a wrong proof, which is the whole point of the gate.
- **Consequence for the pipeline:** Phase B emits **DRAT** and checks with
  `drat-trim` (sound, and CaDiCaL's default tracer). LRAT (native CaDiCaL or via
  `drat-trim -L`) checked by **`cake_lpr`** is the Phase-E verified floor. The
  soundness self-test runs in the proof CI lane as a meta-check on the gate.
- **Carcara** (Alethe) is the theory-layer checker; its rule checks are the
  analogous gate for theory sub-proofs (validated per-theory in Phase C against
  real emitted proofs — Carcara is the arbiter, never a self-emitted "looks-ok").

---

## 2. End-to-end audit (what exists today)

Full per-file findings are in the four audit reports folded into this section.
Citations are `file:line` in the worktree (`proof/implementation` @ `2446991`).

### 2.1 The proof scaffold — almost entirely stub

| Component | State | Evidence |
|-----------|-------|----------|
| `src/proof/ProofManager.{h,cpp}` | **stub**; records `{vector<SatLit> clause, string justification}` to a private vector; **zero call sites** outside unit tests | `ProofManager.cpp:14-22` (export TODO strings); `recordTheoryLemma` `:9-12`; `setSatProofFile` stores an unread path `:5-7` |
| `exportAlethe()` / `exportLFSC()` | **stub** — return `"; … not yet implemented\n"` | `ProofManager.cpp:14-17`, `:19-22` |
| `include/xolver/Proof.h` | **stub** — `isEmpty()→true`, 13 lines, referenced nowhere | `Proof.h:1-13`; `Solver::getProof()` returns `Proof{}` (`src/api/Solver.cpp:848`) |
| `proof-check` CLI | **stub** — prints `[Xolver proof-check] (stub)` | `app/main.cpp:451-454`, dispatched `:554` |
| `--produce-proofs` flag | **no-op** — body is `// TODO: enable proof production` | `app/main.cpp:195-196` |
| `XOLVER_ENABLE_PROOFS` | **inert** — CMake `option(... ON)` + `target_compile_definitions`, but **no `#ifdef` reads it**; proof sources compile unconditionally | `CMakeLists.txt:13`; `src/CMakeLists.txt:97-98` |

**Working templates to mirror:** `model-check` (`app/main.cpp:415-449`) is a thin
value-typed CLI to copy for `proof-check`. `--certify` (`app/main.cpp:122-144,
360-377`) already re-validates and writes a self-contained **sat** certificate —
the closest existing emitter, but sat-only; the unsat analogue is what we build.

### 2.2 The sat-side soundness gate — the design template (mirror this discipline)

There are **two** validators; the task's "ModelValidator" names the wrong one:

- `src/proof/ModelValidator.{h,cpp}` — boolean-structure-only **skeleton**, used
  *only* by unit tests (`ModelValidator.cpp:17-88`); never instantiated in `src/`.
- `src/proof/ArithModelValidator.{h,cpp}` — **the live gate**. Exact (GMP
  `mpq_class` + real-algebraic), **producer-independent** (re-evaluates the
  *original* pre-lowering assertions with its own evaluator — "a bug in the
  producer cannot be masked by the same bug in the checker", `ArithModelValidator.h:16-38`),
  and **conservative 3-valued** `enum Verdict { Satisfied, Violated, Indeterminate }`
  — callers act *only* on `Violated` (`ArithModelValidator.h:41`, `.cpp:10-82`).
  Invoked from `Solver::modelMatchesOriginal()` (`src/api/Solver.cpp:459-473`).

**Design discipline to carry to the unsat side:** value-typed, narrow, an
*independent* checker, and a conservative verdict where the soundness-preserving
default is "cannot confirm" rather than "accept". For unsat that becomes: a proof
is emitted only when it externally checks; otherwise degrade to no-proof.

### 2.3 The conflict/lemma → SAT-core path (where justifications must be captured)

- Theory solvers return a `TheoryCheckResult` carrying **`TheoryConflict { vector<SatLit> clause; }`**
  or **`TheoryLemma { vector<SatLit> lits; LemmaKind kind; }`**
  (`src/theory/core/TheoryAtomTypes.h:83-101`; `LemmaKind { Guess, Entailment, ArraySplit }`).
- `TheoryManager::check` negates conflict reasons into a falsified clause
  (`makeFalsifiedConflict`, `TheoryManager.cpp:408-419`), optionally minimized by
  `ConflictMinimizer` under `XOLVER_SAT_MIN` (`:916, :991` — **a clause-mutating
  step the proof must reflect**).
- `CadicalTheoryPropagator` turns conflicts/lemmas into **external CaDiCaL
  clauses** via `cb_has_external_clause` / `cb_add_external_clause_lit`
  (`src/sat/CadicalTheoryPropagator.cpp:864-884`; enqueued at `:534`/`:550`).
- **No `ProofManager` call exists anywhere on this path.** The *emission boundary*
  carries only a flat `vector<SatLit>` + a free-text tag. Every theory computes a
  richer justification locally and **discards it** at this boundary — that is the
  central gap Phase C closes.

### 2.4 CaDiCaL — propositional proof capability (Boolean core is ready)

- Vendored **CaDiCaL rel-3.0.0** (`7b99c07`) ships native tracers: **DRAT, LRAT**,
  FRAT, VeriPB, IDRUP, LIDRUP, plus `LratChecker` (`third_party/cadical/src/lrattracer.*`,
  `proof.cpp:122-153`).
- **Enable LRAT:** in `CONFIGURING` state (before any `add`/`solve`),
  `solver_->set("lrat", 1)` **then** `solver_->trace_proof(path)`; after an UNSAT
  solve, `solver_->conclude()` then `solver_->close_proof_trace()`
  (`cadical.hpp:852-861, 927`). Order is strict — proofs must be enabled before
  clauses, else only a partial proof is written.
- The Xolver wrapper `CadicalBackend` (`src/sat/CadicalBackend.{h,cpp}`) already
  has a generic `configure(name,value)→solver_->set(...)` passthrough
  (`CadicalBackend.cpp:160`); `trace_proof`/`conclude`/`close_proof_trace` are
  **not yet exposed** and need one-line wrapper methods (Phase B).
- **External-propagation caveat (load-bearing):** with the theory propagator
  connected, theory clauses enter the proof as *original input clauses* "after the
  query line", and reason clauses are *forgettable* (may be deleted). The Boolean
  proof checker must (a) accept theory lemmas as axioms and (b) handle
  `delete_clause` events. Per CaDiCaL `ExternalPropagator` docs in `cadical.hpp`.

---

## 3. Per-theory proof-rule mapping

For each theory: the conflict/lemma construction site, the justification data
*actually in hand there*, its availability, and the target Alethe rule(s).

### 3.1 EUF — **ready now** (proof forest already exists)

- **Where:** `EufSolver::check` (`src/theory/euf/EufSolver_check.cpp:380-451`,
  interface diseq `EufSolver.cpp:645-673`) → `egraph_.explainEquality(a,b)` →
  `mkConflict(TheoryConflict{reasons})`.
- **Engine:** `IncrementalEGraph::explainEquality` (`IncrementalEGraph.cpp:378-536`)
  is an explicit DFS over a **Nieuwenhuis–Oliveras proof-producing congruence
  forest** (`ProofForest.*`). Edges carry `MergeReason { kind, lit, argPairs }`
  with `kind ∈ {AssertedEquality, Congruence, BuiltinEval, ArrayRow1, ArrayConst,
  ArrayRow2, ArrayRow2Cond}` (`EufTypes.h:30-61`).
- **Data availability:** **AVAILABLE NOW, flattened at the boundary.** The walk
  *is* a proof tree (`argPairs` recursion = congruence premises; the path =
  transitivity; `AssertedEquality.lit` = leaf), but `explainEquality` returns a
  flat `ExplainResult { vector<SatLit> reasons }` (`EufTypes.h:116-119`).
- **Target Alethe:** `eq_congruent` (per congruence edge), `eq_transitive` (the
  path), `eq_reflexive`; `symm` as needed. Leaves are the asserted literals.
- **Work:** add a structured/"emit-steps" mode to the existing walk. **No new
  reasoning.** This single refactor is ~70% of Datatype and Combination too.

### 3.2 LRA — **clean Farkas certificate** (target `la_generic`)

- Simplex infeasibility yields a Farkas combination (nonneg. rational multipliers
  of the asserted bounds summing to `0 ≤ -1`). Alethe **`la_generic` takes those
  rational coefficients as rule arguments** — a direct match.
- **Where:** `GeneralSimplex::explain{Lower,Upper,Immediate}Conflict`
  (`src/theory/arith/logics/lra/GeneralSimplex.cpp:827-890`) → `getConflict()`
  (`GeneralSimplex.h:130`) → `TheoryConflict` in `LraSolver.cpp:255-285`. Returns
  `vector<BoundReason{var,isLower,SatLit}>` — **no coefficient field**.
- **Data availability:** **AVAILABLE-BUT-DISCARDED (resident).** The Farkas
  multipliers *are* the infeasible basic variable's tableau row; the exact
  `mpq_class` coefficient is read at the construction site (`GeneralSimplex.cpp:836-838`,
  `const mpq_class& a = e.coeff`) to *select* which bound enters the conflict,
  then dropped — only the `SatLit` survives. The full row `tab_.row(r)` is still
  resident, so capturing it + the violated bound gives a complete certificate.
- **Target Alethe:** `la_generic` (the Farkas combination), `la_disequality`,
  `la_rw_eq`, `la_mult_pos`/`la_mult_neg` for strict/eq handling.

### 3.3 IDL / RDL — **negative cycle = Farkas certificate** (cross-theory easiest)

- A Bellman–Ford negative cycle is itself a Farkas certificate with all
  multipliers ≡ 1: summing the cycle's difference constraints yields `0 < 0`.
- **Where:** `BellmanFord::runFull → BfResult{cycle, dist}` (`extractCycle`,
  `src/theory/arith/logics/dl/BellmanFord.h:26-77`) → `buildConflict(cycle, graph)`
  (`DlExplanation.h:16-28`) at `IdlSolver.cpp:243-246` / `RdlSolver.cpp:226-229`.
  Each `DlEdge{from,to,weight,reason,id}` (`DifferenceGraph.h:19-25`) holds an
  exact weight (`IdlWeight=mpz_class`; `RdlWeight={mpq_class c; int deltaCoeff}`).
- **Data availability:** **AVAILABLE-NOW.** The full cycle (edges + weights +
  order) is held in `bfResult.cycle` + `graph_` at emission; `buildConflict` keeps
  only the deduped literals. Structurally the simplest certificate in the solver —
  capture `bfResult.cycle` and emit.
- **Target Alethe:** `la_generic` with unit coefficients over the cycle's
  difference constraints (DL is linear arithmetic).

### 3.4 LIA — **branch trivial; cut coefficients exist; some holey**

- **Where (LP infeasibility):** reuses the LRA Farkas path verbatim
  (`gs_.getConflict()`).
- **Branch lemma:** `LiaSolver::buildBranchSplitLemma`
  (`LiaSolver_integrality.cpp:504-552`) → `(x≤⌊v⌋) ∨ (x≥⌈v⌉)`. **AVAILABLE-NOW**;
  a branch split is a trivially-valid tautology.
- **Gomory/GMI cut:** `generateGomoryCut` (`LiaSolver_integrality.cpp:392-502`) via
  `deriveGomoryCut`/`deriveGmiCut` (`logics/lia/GomoryCut.{h,cpp}`) returns
  `GomoryCutResult{vector<mpq_class> gamma; mpq_class rhs}` (`GomoryCut.h:43-47`) —
  exact rational cut coefficients, with a unit-tested validity argument — then
  collapsed to one cut atom + reason literals (`:501`). **AVAILABLE-BUT-DISCARDED.**
- **Target Alethe:** `la_generic` for the LP-relaxation Farkas, a divisibility/cut
  step for the GMI cut, and a branch tautology for splits. `lia_generic` is the
  *holey* catch-all (a checker may not fully verify it), so tight cuts that must be
  checked need the explicit cut derivation rather than the hole.

### 3.5 Arrays — **eager merges ready; lazy splits discard the instance**

- **Eager** Row1/Row2/Const/Row2Cond merges land in the EUF proof forest with
  their axiom kind + equality chains retained (`ArrayReasoner.cpp:450-650`,
  `EufTypes.h:44-51`) → certifiable via the EUF path.
- **Lazy** SAT-split / extensionality lemmas (`ArrayReasoner::instantiateLemma`,
  `:651-860+`) return only `vector<SatLit>`; the axiom **schema, full
  substitution, fresh Skolem witness** (`makeFreshVariable("__nlc_ext_idx")`,
  `:840`) and **refinement round** (`XOLVER_AX_REFINE`) are discarded.
  `LemmaKind` can't even distinguish Row2 from extensionality.
- **Target Alethe:** read-over-write and extensionality are theory-specific; in
  Alethe these are typically `hole`-wrapped or expressed via instantiation +
  EUF. **Hardest non-nonlinear theory**; needs new per-lemma schema/substitution
  bookkeeping. Candidate for partial degraded mode at first.

### 3.6 Datatypes — **axiom known but discarded** (parasitic on EUF)

- `DtReasoner::checkConflict`/`instantiateLemma` (`DtReasoner.cpp:254-389`,
  `:505-660+`) fire the Reynolds–Blanchette axiom family (constructor clash,
  tester consistency, injectivity, selector projection, exhaustiveness,
  acyclicity). The code knows the exact axiom/ctor/field-index/cycle, but emits
  flat concatenated `explainEquality` reasons.
- **Target Alethe:** EUF rules for the reason chains + a thin DT step per axiom
  schema. **Medium**; recovers once a per-lemma schema tag is added.

### 3.7 Combination (Nelson–Oppen) — **glue is ready; depends on per-theory sub-proofs**

- Interface-equality propagation returns `SharedEqualityPropagation { a, b,
  reasons }` (`TheorySolver.h:108-112`); the glue builds a per-theory tautology
  lemma `(¬reasons ∨ eqLit)` (`TheoryManager.cpp:984-1004`). **Reasons retained.**
- The **Purifier** mints `bridge_N` with a retained back-map and emits definitional
  bridge equalities `makeEq(fresh, original)` (`Purifier.cpp:81-93, 376-480`) —
  trivially certifiable **Tseitin-style extensions**.
- A second proof forest over shared terms backs interface conflicts
  (`ExplainableRollbackUnionFind::explain`, `SharedEqualityManager.cpp:39-58`);
  `conflictIsGenuine` (`TheoryManager.cpp:433+`) already re-checks them — an
  in-tree proof-checking skeleton.
- **Target Alethe:** definitional steps for bridges + per-theory sub-proofs of the
  interface lemmas (recursively EUF). **Easy/medium** once EUF is structural.

### 3.8 Nonlinear & mixed arithmetic — NRA, NIA, NIRA/LIRA

These are the hard lanes. LRA/LIA/IDL/RDL are covered in §3.2–3.4; here are the
ones that start in degraded no-proof mode.

**NRA (CDCAC / Collins–Lazard, libpoly) — ABSENT on the production path.**
- **Where:** `NraSolver::stageCac` (`logics/nra/NraSolver_cac.cpp:398-407`) builds
  the conflict purely from `res.unsatCore` *constraint indices*. `CacResult`
  (`cac/CacEngine.h:55-76`) carries `{status, model, unsatCore, unknownSample}` —
  the `CacCovering` (excluded intervals with exact algebraic endpoints,
  `cac/Covering.h`) lives **inside** the recursion and is never surfaced;
  `ReasonManager::minimize(Covering)` reduces it to `vector<SatLit>`.
- **A rich certificate design exists but is unwired:** `core/CdcacCertificate.h`
  has `CoveringCertificate`, `CellCertificate`, `SignInvariantCertificate`,
  `LazardCellCertificate` with per-step completeness flags + an `isComplete()`
  gate. But it is populated only on the **gated experimental** `CdcacCore` engine
  (`XOLVER_NRA_LAZARD_CELL_CERT`, `XOLVER_NRA_PREELIM`; `CdcacCore.cpp:1938`),
  validated **debug-only** (`#ifndef NDEBUG`), checked by `CdcacProofChecker` only
  from **unit tests**, and `CdcacProof.h` (serializable V7 proof) is **never
  populated** on a solve path. `PendingConflict::certificate` is always `nullopt`.
- **Verdict:** richest certificate *design*, weakest *wiring*. A checkable
  CAD/CDCAC cell-exclusion certificate is itself an open research problem →
  **degraded no-proof** initially; the `CdcacCertificate` scaffolding is the
  long-term path if/when it is wired to the production conflict + serialized.

**NIA (NIA-Core + reasoners + bit-blast) — mixed.**
- **ABSENT (opaque):** bit-blast (`stageBitBlast`,
  `NiaSolver_bitblast.cpp:254-260` → `BitBlastSolver::buildCompleteConflict`
  `:99-147`; the SAT UNSAT is opaque, no constraint↔CNF map retained — a proof
  would need bit-blasting soundness lemmas + a DRAT/LRAT subproof); Omega test
  (`reasoners/OmegaTest.h:34`, returns a bare `enum {Unsat, SatOrUnknown}`);
  same-poly/domain/difference conflicts (`NiaSolver_refute.cpp:123, 203, 222`).
- **AVAILABLE-BUT-DISCARDED:** `GcdDivisibilityReasoner`
  (`reasoners/GcdDivisibilityReasoner.cpp:34-36`, gcd witness),
  `DioReasoner` (`:331`, per-var `Cong{residue,modulus}` congruence chain),
  `ModularResidueReasoner` (`:1263`, Hensel/Newton lifting witnesses),
  `FarkasOrSolver` (`NiaSolver_farkas.cpp`, holds Farkas `rayPerBlock` but as a
  SAT-*model* constructor; refutation path returns `nullopt`).
- **Branch:** `buildBranchLemma` (`NiaSolver_branch.cpp:177-187`) — trivial split.
- **Verdict:** algebraic reasoners are recoverable (each needs its own checkable
  rule — gcd/divisibility, Diophantine congruence, modular lifting); bit-blast and
  Omega are opaque. Mostly **degraded** at first, with the algebraic reasoners as
  the incremental wins.

**NIRA / LIRA (mixed) — ABSENT.**
- `LiraSolver::check*` (`logics/mixed/LiraSolver.cpp:146-161`) uses a MILP engine
  whose dual/shadow-price (Farkas) data is not surfaced; conflict is LP-leaf or
  all-active reason literals. `NiraSolver` (`mixed/NiraSolver.cpp:117-118, 937-946`)
  delegates subproblems to NIA/NRA and inherits their opacity. No own witness.
- **Verdict:** literal-set aggregators over delegated checks → **degraded**, and
  they improve only as their NIA/NRA/LRA sub-lanes gain certificates.

### 3.9 Propositional core & clausification (all theories)

- **SAT core:** `resolution`, `th_resolution`, `contraction`, `tautology`,
  `reordering` — but in practice emitted as **LRAT** from CaDiCaL (Phase B) and
  optionally translated to Alethe `resolution` in Phase D.
- **Clausification/Tseitin:** `and`, `or`, `not`, `implies`, and the polarity
  rules `and_pos`, `and_neg`, `or_pos`, `or_neg`, `implies_pos`, `implies_neg` —
  these justify the CNF encoding (trust-boundary item 3 in §1.3), sourced from the
  Atomizer (`src/expr/`/frontend).

---

## 4. Gap analysis & readiness ranking

| Rank | Theory | Certificate data today | Effort | Phase |
|-----:|--------|------------------------|--------|-------|
| 1 | **EUF** | proof forest **exists** (`ProofForest`), walked every conflict; only flattened to `vector<SatLit>` | low (emit steps) | C.1 |
| 1 | **IDL/RDL** | **AVAILABLE-NOW** — negative cycle `bfResult.cycle` + exact weights held at emission | low (capture cycle) | C.2 |
| 3 | **LRA** | **discarded-but-resident** — Farkas row `tab_.row(r)` (`mpq_class`) read at conflict site | med | C.1 |
| 4 | **Combination glue** | reasons retained; bridges definitional; `conflictIsGenuine` re-checker exists | low/med (needs EUF) | E |
| 5 | **LIA** | branch trivial; Gomory `GomoryCutResult{gamma,rhs}` exact but discarded | med/high | C.2 |
| 6 | **Datatype** | axiom instance known but discarded; parasitic on EUF | med | C.3 |
| 7 | **NIA (algebraic)** | gcd/Diophantine/modular witnesses computed then dropped | high | C.4 |
| 8 | **Array** | eager merges ok; lazy splits discard schema + Skolem witness + refine round | high | C.3 |
| 9 | **NIA (bit-blast/Omega), NIRA/LIRA** | opaque SAT UNSAT / bare boolean / unsurfaced MILP dual | high/research | C.4 / degraded |
| 10 | **NRA** | CAD/Lazard cell certs — rich `CdcacCertificate` design but **unwired** (gated/debug/tests only) | research | C.4 / degraded |

**Degraded no-proof policy (the soundness floor).** For NRA cell certificates and
any lemma whose checkable certificate is not yet tractable, the solver emits
`unsat` **without** a proof and logs it as *no-proof* — it must **never** emit a
proof Carcara/lrat-check rejects. An unverifiable proof is a release blocker of
the same severity as an unsound verdict. This mirrors `ArithModelValidator`'s
"act only on the definite verdict" discipline on the unsat side.

**Cross-cutting refactor that unlocks the most:** give EUF's explain path a
structured "emit-steps" return instead of `ExplainResult.reasons`. Datatype and
Combination both bottom out in `explainEquality`, so structurally certifying EUF
is most of their work too. Sequence EUF first in Phase C for that leverage.

**Soundness levers to reflect in any proof:** `XOLVER_SAT_MIN` clause
minimization mutates emitted clauses (`TheoryManager.cpp:916, 991`); the
stale-interface-merge guard (`TheoryManager.cpp:343-346`) and `conflictIsGenuine`
gate interface conflicts. A proof must be built from the *post-minimization,
post-guard* clauses actually fed to CaDiCaL, not the pre-minimization reasons.

---

## 5. Locked corpus & phase gates

- **Corpus:** `corpus/UNSAT-CORPUS.txt` — 46 files (2 smallest non-known-fail
  `:status unsat` per logic dir), spanning all 23 regression lanes; regenerable
  via `corpus/select_corpus.sh`. This is the external-checking reference set for
  Phases B–E.
- **Every phase ends green on:** `cmake --build . -j2 && ctest &&
  python3 tools/regression/run_regression.py --root tests/regression --solver build/bin/xolver`
  → **0 UNSOUND**, plus (proofs ON) **0 unverifiable proofs** over the corpus, and
  (proofs OFF) **decided-count delta = 0** vs. the pre-work binary.
- **Phase A gate:** docs-only change → solver path untouched → trivially green
  (verified: `git diff --name-only origin/main..HEAD` is `docs/` only).

---

## 6. Decisions that flow into B–E

1. **Flip `XOLVER_ENABLE_PROOFS` to default-OFF and make it real** (`#ifdef`-gate
   the proof recording + a runtime `XOLVER_ENABLE_PROOFS=1` env switch per repo
   convention). Today it is ON and gates nothing. (Phase B.)
2. **Phase B:** expose `CadicalBackend::enableProof(path, lrat=false)` and thread it
   through `ProofManager::setSatProofFile`; emit **DRAT** and check `CNF ∪ lemmas ⊢ ⊥`
   with the adversarially-sound **`drat-trim`** on the corpus (treating theory
   lemmas as axioms). LRAT + `cake_lpr` is the Phase-E verified upgrade.
3. **Phase C:** structured EUF explain first (→ `eq_congruent`/`eq_transitive`),
   then LRA `la_generic`, then IDL/RDL, LIA, Datatype, Array; NRA/NIA degraded.
4. **Phase D:** `exportAlethe()` assembles theory sub-proofs + the (translated or
   linked) Boolean core; real `proof-check` shells out to Carcara + lrat-check
   with non-zero exit on failure; `Proof` becomes a real value type.
5. **Phase E:** Nelson–Oppen glue steps; CI lane (`XOLVER_ENABLE_PROOFS=ON`) that
   externally checks every corpus proof, red on any reject; arch rule if proof
   emitters introduce a new layering boundary.
