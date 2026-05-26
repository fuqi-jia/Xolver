# NIA Bit-Blasting Module — Design Spec

**Date:** 2026-05-26
**Author:** fuqi-jia (migration of the BLAN solver into Zolver)
**Status:** Approved for planning

## 1. Goal

Migrate the core algorithms of the standalone **BLAN** QF_NIA solver
(`/mnt/d/D_Study/BUAA/projects/BLAN`, paper DOI `10.1145/3597926.3598034`) into
Zolver as a new subsystem `src/theory/arith/bit_blast/`, wired in as one stage
of the NIA `Reasoner` pipeline. The migration covers the **two named parts**:

1. **Space sizing** — compute *where solutions can be*: per-variable bit-width
   assignment driven by variable bounds and coefficient/multiplication
   heuristics (BLAN `Collector` + `Decider`).
2. **Bit-blasting** — encode NIA constraints into CNF for CaDiCaL, including the
   **Greedy-Addition** reordering that sorts addition chains by ascending
   bit-width to reduce redundant bit-width usage on large-scale instances
   (BLAN `blaster_transformer::SortingAddition` + `blaster_solver`).

Out of scope (explicitly excluded per the scope decision): the NLSAT
**Resolver** refinement loop, ICP solver, and BLAN's three interchangeable
comparison abstractions (we ship one sound signed-compare encoding).

## 2. Non-negotiable soundness contract

Zolver invariant: *NIA is soundness-over-completeness; never emit UNSAT from
incomplete reasoning; every `Sat` is validated by exact integer arithmetic.*

### 2.0 What gets encoded (self-contained, no hidden dependency on `cs`)

`BitBlastSolver` encodes **two** things into its independent SAT instance, and
its soundness does **not** rely on `cs` happening to contain the bound atoms:

1. **Every constraint in `cs`** (the active normalized constraints; in
   integration, `NiaSolver::normalized_`).
2. **The `DomainStore` restrictions** of each variable — `x ≥ lb`, `x ≤ ub`, plus
   finite-set / exclusion constraints — emitted explicitly via
   `encodeDomainBounds`.

**Encoded variable set.** The encoded variables are `vars(cs) ∪ {variables that
carry any DomainStore restriction}` — *not* just `vars(cs)`. A variable that
appears **only** in `DomainStore` (e.g. a `z` with an empty/contradictory domain
introduced by earlier reasoning) is still allocated a bit-vector, encoded, and
validated. Otherwise a domain-only inconsistency could be silently missed and we
would return a spurious SAT. `SpaceEstimator::estimate` therefore unions the
restricted-domain variables into its `BitWidthPlan`.

Consequently the SAT search space **equals** the box `[lb,ub]ⁿ` intersected with
`cs` (not the raw two's-complement width range). A candidate model is accepted
only if it (a) passes `IntegerModelValidator` over `cs` *and* (b) lies inside the
`DomainStore` box (`modelInDomains`) for **every** restricted variable. This
makes the box-confinement **local and explicit** rather than depending on the
cross-stage invariant "`normalized_` already contains the bounds."

> **Why this matters (reviewer's counterexample):** with `cs = {x·y = 6}` and
> bounds only in `DomainStore` (`x,y ∈ [0,6]`), a 4-bit width admits `[-8,7]`, so
> a naive "encode `cs`, validate `cs`" would accept `x=-1, y=-6`. Explicitly
> encoding `x≥0 ∧ x≤6 ∧ y≥0 ∧ y≤6` and re-checking `modelInDomains` rejects it.

`DomainStore` is still also used (non-semantically) for **width sizing** and the
**`boxIsComplete`** predicate. Its soundness (bounds never exclude a real
solution) is trusted — exactly as `stageBounded` already trusts it.

### 2.1 The two directions

- **SAT** is accepted only when `IntegerModelValidator.validate(model, cs) ==
  Valid` **and** `modelInDomains(model, domains)` both hold. A model produced
  under a deliberately narrow width may be a two's-complement **overflow
  artifact** or fall outside the box; either check rejects it.
- **UNSAT** (`Conflict`) is emitted **only** when the box is *provably complete*.
  The encoder uses width-growing arithmetic (`add`→`max+1`, `mul`→`wa+wb`), so
  with each leaf width covering its `[lb,ub]` the entire polynomial evaluation is
  **exact (overflow-free)**, and the explicitly-encoded bounds confine the search
  to the box. Therefore:

  > `boxIsComplete` ⇔ every **encoded** variable (i.e. every var in
  > `vars(cs) ∪ restricted-domain-vars`) has a hard finite lower **and** upper
  > bound in `DomainStore`, and its leaf width is sized to cover that range.

  Soundness argument: the encoded bounds restrict the search to `[lb,ub]ⁿ`;
  `bitsToCover` makes each width range `⊇ [lb,ub]` so no in-box value is
  unrepresentable; `DomainStore` (trusted sound) guarantees every real solution
  of `cs` lies in `[lb,ub]ⁿ`. Hence *(encoded `cs` ∧ box) UNSAT ⟺ `cs` has no
  integer solution*. The conflict clause is the disjunction of the **negated
  reason literals of every encoded justification** — *both* the `cs`-constraint
  reasons (including the nonlinear atoms) *and* the reasons of every encoded
  `DomainStore` restriction (lower, upper, finite-set, exclusions) — because the
  infeasibility is a property of the whole conjunction. (Including the
  nonlinear-atom reasons is what stops the conflict from wrongly claiming the
  interval alone is infeasible, e.g. for `x·x = 2 ∧ -3≤x≤3`.) **Every encoded
  restriction must contribute a usable reason: if *any* encoded constraint or
  bound lacks one (empty reason list, or a literal with `var == 0`), the stage
  must NOT silently drop it — that would yield an unsound partial conflict such
  as `¬A ∨ ¬B` when the real infeasibility also needed an unjustified bound.
  Instead it downgrades to `Unknown`.** Likewise if the normalized clause is
  empty or self-contradictory. This is a sound theory lemma: every listed
  literal is currently true, so the clause is currently falsified.
- In every other case (some variable unbounded, or widths capped for speed,
  or a candidate fails either acceptance check) the stage returns `nullopt`
  (continue pipeline) or `Unknown` — **never** UNSAT.

## 3. Two operating modes

| Mode | When | Leaf widths | SAT | UNSAT |
|---|---|---|---|---|
| **Complete** | all vars hard-bounded | cover `[lb,ub]` exactly (exact, overflow-free) | model (validated) | **sound UNSAT** |
| **Heuristic** | some var unbounded / widths capped | BLAN-style guessed widths (overflow allowed) | model if validates, else grow/Unknown | **Unknown** (grow widths up to cap, never UNSAT) |

The heuristic mode is exactly BLAN's "where solutions are likely" sizing: it
finds models fast on satisfiable large instances by guessing small widths and
growing on demand.

## 4. Architecture & components

New directory `src/theory/arith/bit_blast/` (auto-globbed by
`src/CMakeLists.txt`'s `theory/**/*.cpp` / `*.h`, no build edits).

```
bit_blast/
├── BitVec.h               — two's-complement bit-vector over SatLit
├── BitBlastEncoder.{h,cpp}— CNF engine: gates, add/sub/mul/pow, signed compare
├── SpaceEstimator.{h,cpp} — Part 1: bound/coefficient sizing → BitWidthPlan
├── PolyBitBlaster.{h,cpp} — adapter: PolyId terms → BitVec + Greedy-Addition sort
└── BitBlastSolver.{h,cpp} — orchestrator: owns CaDiCaL, encode→solve→validate→refine
```

### 4.1 `BitVec` (replaces BLAN `blast_variable`)

```cpp
namespace zolver::bitblast {
struct BitVec {
    std::vector<SatLit> bits;   // bits[0]=LSB ... bits.back()=MSB (sign), two's complement
    bool     isConst = false;
    mpz_class constValue = 0;   // valid iff isConst
    unsigned width() const { return static_cast<unsigned>(bits.size()); }
    SatLit   sign()  const { return bits.back(); }
};
}
```

### 4.2 `BitBlastEncoder` (rewrite of BLAN `blaster_solver`/`blaster_operations`)

Owns a non-owning `SatSolver&` (the orchestrator's independent CaDiCaL). Holds
two clamped literals `true_`/`false_`. Tseitin gates (`andGate/orGate/xorGate/
iteGate`) each allocate a fresh var and emit the standard clause set.
Arithmetic is two's complement with **width growth**: `add`→`max(wa,wb)+1`
(ripple-carry full adders), `sub(a,b)`=`add(a, neg(b))`, `neg`=invert+add-one,
`mul`→`wa+wb` (shift-add of partial products), `mulConst`/`powConst` as
constant-folded specializations. Relations reduce to `relZero(value, rel)`
because every constraint is in `p rel 0` form; the value bitvec's own sign bit
and `isZero` give exact signed comparisons (no overflow, since the value is
represented at full width).

### 4.3 `PolyBitBlaster` (rewrite of BLAN `blaster_transformer`) — Greedy Addition

For a constraint `p rel 0`:
1. `kernel.terms(p)` → monomials `{coefficient, [(VarId,exp)…]}`.
2. Each monomial → `mulConst(coeff, powConst(v1,e1) · powConst(v2,e2) · …)`.
3. **Greedy Addition**: collect the monomial `BitVec`s, then while >1 remain,
   `std::sort` by ascending `width()` and fold the two smallest with `add` —
   the literal port of BLAN's `SortingAddition` comparator and `doMathTerms`
   while-loop. Summing smallest-first keeps intermediate widths minimal.
4. `encoder.assertLit(encoder.relZero(sum, rel))`.

### 4.4 `SpaceEstimator` (rewrite of BLAN `Collector` + `Decider`) — Part 1

Input: the normalized constraints + `DomainStore`. Output:

```cpp
struct BitWidthPlan {
    std::unordered_map<std::string, unsigned> width;  // per variable
    bool boxIsComplete = false;
};
```

Rules:
- **Variable set** = `vars(cs) ∪ {vars carrying any DomainStore restriction}`.
  Domain-only variables are included so they get encoded and validated (§2.0).
- Hard-bounded var `[lb,ub]` → `width = bitsToCover(lb,ub)` (two's-complement
  bits to represent both endpoints).
- Unbounded/loose var → heuristic start width from BLAN **Coefficient-Matching**
  (max `|coefficient|` seen with the var via `kernel.terms`) and
  **Multiplication-Adaptation** (base width adapts to multiplication count),
  capped at `K`. (Vote / Distinct-Graph heuristics optional, deferred.)
- `boxIsComplete = true` iff *every* variable in that set has both hard bounds.
- A `grow(plan, maxBW)` helper **doubles** each width (capped at `MaxBW`) for the
  heuristic refinement loop. Doubling — rather than a small additive step — is
  what lets the loop actually reach large widths within a few iterations
  (QF_NIA solutions can be large); an additive `+δ` step with a low iteration
  cap would leave a high `MaxBW` unreachable.

### 4.5 `BitBlastSolver` (the stage body; rewrite of BLAN `searcher` + loop)

```cpp
struct BitBlastResult {
    enum class Status { Sat, UnsatComplete, Unknown } status;
    IntegerModel model;                       // valid iff Sat
    std::optional<TheoryConflict> conflict;   // valid iff UnsatComplete
};
```

`solve(cs, domains, validator)` (see §2.0). Defaults: `maxBW_ = 256`,
`maxIters_ = 6`, doubling growth.
1. `SpaceEstimator` → `BitWidthPlan` (from `cs` + `domains`).
2. Fresh `createSatSolver()`; encoder + adapter over it; `mkVar(width)` per
   variable; assert **every** constraint in `cs`; then `encodeDomainBounds` to
   also assert each variable's `DomainStore` box (`x≥lb`, `x≤ub`, finite-set,
   exclusions). The search space is now exactly `[lb,ub]ⁿ ∩ cs`.
3. `sat->solve()`.
4. **Sat**: reconstruct each var's integer value from its bits (two's
   complement) → `IntegerModel`; accept iff `validator.validate(model, cs) ==
   Valid` **and** `modelInDomains(model, domains)` ⇒ `{Sat, model}`; otherwise
   treat as overflow / out-of-box artifact → grow & retry.
5. **Unsat**: `boxIsComplete` ⇒ build the conflict from the **negated reasons of
   every encoded justification** — all `cs` constraints **and** all
   `DomainStore` bounds (`buildCompleteConflict(cs, domains)`, §2.1); a non-empty
   normalized clause ⇒ `{UnsatComplete, conflict}`, otherwise ⇒ `{Unknown}`.
   If not complete ⇒ `grow(plan, maxBW_)` (doubling) and retry from step 2; on
   `maxIters_` cap ⇒ `{Unknown}`.
6. **Unknown** from CaDiCaL ⇒ `{Unknown}`.

### 4.6 Integration into `NiaSolver`

- New member method `std::optional<TheoryCheckResult> stageBitBlast(
  TheoryLemmaStorage&, TheoryEffort)` and a `BitBlastSolver bitBlast_` member.
- Registered in the constructor **after `nia.bounded`, before
  `nia.local-search`** (cheap exact enumeration first; bit-blast as the scalable
  complete/semi-complete attempt before heuristic local search and branching).
- Gated to `TheoryEffort::Full` only (constructed as a full-effort
  `CallbackReasoner`) to avoid firing on every propagation.
- Maps `BitBlastResult`: `Sat`→set `currentModel_`, `consistent()`;
  `UnsatComplete`→`mkConflict`; `Unknown`→`nullopt` (continue pipeline).
- A member toggle `bool enableBitBlast_ = true;` allows disabling; when the
  applicability guard finds nothing to size, the stage returns `nullopt`.

## 5. Testing

- **Unit** (`tests/unit/test_bit_blast.cpp`, doctest): gate truth tables;
  add/sub/mul/pow correctness checked by solving with CaDiCaL and reading the
  model; `relZero` for each relation; Greedy-Addition narrows the max
  intermediate width on a crafted equal-width chain vs. unsorted folding;
  `SpaceEstimator` widths and `boxIsComplete`; end-to-end `BitBlastSolver` for a
  bounded SAT instance (model validates), a complete-box UNSAT instance, and an
  unbounded UNSAT instance (returns `Unknown`, never UNSAT).
- **Regression**: port BLAN `test/*.smt2` into `tests/regression/nia/`
  (multi-term multiplication + addition chains); run `tools/run_regression.py`
  against the z3/cvc5 oracle. **Acceptance: 0 UNSOUND, baseline still green**
  (ctest 15/15, unit all pass, regression no new failures).

## 6. Risks

- **Encoding bugs** in the hand-written adder/multiplier are the main risk; TDD
  against CaDiCaL on small known values mitigates this.
- **Width blow-up** in complete mode for high-degree/large-coefficient inputs;
  bounded by an encoding-size cap that downgrades to heuristic (no UNSAT) when
  exceeded.
- The `IntegerModelValidator` is the final soundness backstop for SAT; UNSAT
  soundness rests entirely on the `boxIsComplete` predicate + width-growing
  exactness argument in §2.
