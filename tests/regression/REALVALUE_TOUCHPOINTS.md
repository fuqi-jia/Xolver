# RealValue Migration — Touchpoints Worklist (Phase 0 output)

Produced by Phase 0 of `~/.claude/plans/realvalue-unification.md`. This is the
authoritative work-list that Phase 1 (model-output funnel) and Phase 2 (atom
RHS / tableau / conflicts) consume. Line numbers are as of base commit
`ba53c3d` (post-ArithSolverBase migration). **Re-grep before editing — the
architecture-refactor agent may move these.**

## Representation B → RealValue (CDCAC `RealAlg`/`AlgebraicRoot`) — Phase 1

`RealAlg` is used in (grep `RealAlg`):

- `src/theory/arith/nra/core/CdcacValue.h` — definitions (`RealAlg`, `AlgebraicRoot`, `Bound`, `ExtRealAlg`, `SamplePoint::values`, `RootSet`)
- `src/theory/arith/nra/backend/AlgebraBackend.h` — `isolateRealRoots` return, `compareRealAlg`
- `src/theory/arith/nra/backend/LibpolyBackend.{h,cpp}` — root isolation, sign-at-algebraic, refinement
- `src/theory/arith/nra/core/CdcacCore.{h,cpp}` — `sampleAt`, `solveLevel`, `mergeRoots`
- `src/theory/arith/nra/core/CdcacCertificate.h`, `CdcacCell.h`, `CdcacObjective.h`
- `src/theory/arith/nra/engine/SampleHeuristic.cpp`

Phase 1 step 2: replace `RealAlg`→`RealValue`, `AlgebraicRoot`→`AlgebraicNumber`;
make `CdcacValue.h` a thin re-export; `Bound`/`ExtRealAlg`→`ExtendedRealValue`
(open/closed bit moves to the consuming `Interval`).

## Model-output funnel — Phase 1

| File | Line | Current | Target |
|---|---|---|---|
| `src/theory/core/TheorySolver.h` | 72–74 | `struct TheoryModel { unordered_map<string,string> assignments; }` | `unordered_map<string,RealValue> numericAssignments;` + `unordered_map<string,bool> boolAssignments;` |
| `include/nlcolver/Model.h` | 26, 31 | `unordered_map<uint32_t,string> values_` | `unordered_map<uint32_t,RealValue>` |
| `src/api/Solver.cpp` | getValue/getModel | string reconstruct via `std::stoll`/`mkReal(string)` | serialize via `RealValue::toSmtLib2`; add `mkAlgebraicReal` |
| getModel() overrides | — | per-solver string build | construct `RealValue` |

`getModel()` overrides to update (grep `getModel`): `LiaSolver.{h,cpp}`,
`LiraSolver.{h,cpp}`, `LraSolver.{h,cpp}`, `NiraSolver.{h,cpp}`,
`NraSolver.{h,cpp}` (NRA additionally emits `fromAlgebraic`).

> NOTE: the ArithSolverBase refactor (parallel agent) may hoist `getModel()`
> into the base class. If so, Phase 1 step 4 edits **one** base method instead
> of 6 overrides — re-check `ArithSolverBase` before starting.

## Representation A → RealValue (`mpq_class rhs`) — Phase 2 (RHS only)

Widen the RHS *scalar* only; `LinearFormKey`/monomial **coefficients stay
`mpq_class`** (out of scope per plan).

| File | Line | Field |
|---|---|---|
| `src/theory/core/TheoryAtomTypes.h` | 40 | `LinearAtomPayload::rhs` |
| `src/theory/core/TheoryAtomTypes.h` | 46 | `PolynomialAtomPayload::rhs` |
| `src/theory/core/TheoryAtomRegistry.h` | 61, 79 | atom record `rhs` (+ extend `std::hash`) |
| `src/theory/arith/linear/LinearAtomManager.h` | 69 | `rhs` |
| `src/theory/arith/linear/LinearConstraintTypes.h` | 46 | `rhs = 0` |
| `src/theory/arith/linear/LinearModelValidator.h` | 21 | `rhs` |
| `src/theory/arith/integer/IntegerReasoner.h` | 18 | `rhs` |
| `src/theory/arith/lia/InternalMilpEngine.h` | 29 | `rhs` (+ `value(int var)`) |
| `src/theory/arith/lia/LiaSolver.h` | 77 | inner `LinAtom::rhs` |
| `src/theory/arith/lra/LraSolver.h` | 74, 117 | inner `LinAtom::rhs` |
| `src/theory/arith/lra/SparseTableau.h` | 30 | tableau `rhs = 0` |
| `src/theory/arith/lra/LraSolver.cpp` | 371 | local `rhs` |
| `src/theory/arith/lira/LiraSolver.h` | 65 | inner `LinAtom::rhs` |
| `src/theory/arith/nia/NiaTypes.h` (`ActiveNiaConstraint`) | — | `rhs` |
| `src/theory/arith/nira/NiraSolver.cpp` | 274 | local `rhs` |
| `src/theory/arith/rdl/RdlSolver.h` | 48 | `rhs` |
| `src/theory/arith/idl/IdlSolver.cpp` | 84 | local `rhs` |
| `src/theory/arith/search/CandidateModelSearch.{h,cpp}` | — | `evalTerm::numValue` widen + strategy 10e (CDCAC bracket midpoints) |

Sites that legitimately stay `mpq_class` (do NOT widen): atom-extraction
locals (`ArithAtomExtractor.cpp:38,75`), `CdcacObjective.h:66` (objective
constant), `IntLinearEqualityCoreHNF.cpp:70` (internal SNF scalar), and all
`LinearFormKey` coefficients.

## libpoly Algebraic API Survey (de-risks Phase 1 delegation)

`third_party/libpoly/include/algebraic_number.h` (+ C++ wrapper
`include/polyxx/algebraic_number.h`) provides the full set needed — **no gaps**:

- construct: `lp_algebraic_number_construct`, `_construct_copy`,
  `_construct_zero/_one`, `_construct_from_integer`, `_construct_from_rational`,
  `_construct_from_dyadic_rational`
- arithmetic: `lp_algebraic_number_add/_sub/_mul/_div/_neg`
- compare: `lp_algebraic_number_cmp`, `_cmp_rational`, `_cmp_integer`,
  `_cmp_dyadic_rational`
- sign / approx: `lp_algebraic_number_sgn`, `_to_double`

Phase 1 routes `RealValue` algebraic arithmetic/compare through a
`LibpolyAlgebraicBackend` wrapping these. Rational-vs-algebraic uses
`_cmp_rational` / `_construct_from_rational` directly (no need to fabricate a
`q·x − p` defining poly). Defining-poly access for serialization /
`AlgebraicNumber.coefficients` round-trips via libpoly's `lp_upolynomial_*`.

## Phase-0 deviations from the literal plan (intentional)

1. **Tests skipped, not failing in CI.** The plan's Phase-0 gate says
   `test_realvalue.cpp` should *run and fail*. But `tests/unit/*.cpp` is
   `GLOB_RECURSE`'d into the single `nlcolver_unit_tests` binary = the `unit`
   ctest label, so failing cases would turn shared `main` red and break the
   parallel agent's "ctest 15/15" gate. Resolution: every case is
   `* doctest::skip()` inside `TEST_SUITE("realvalue")`. Default `ctest` stays
   green; the designed-failure is observable on demand with
   `nlcolver_unit_tests --no-skip -ts=realvalue`. **Phase 1 deletes the skip
   decorators** so the suite runs by default and must pass.

2. **`void* libpolyHandle` omitted from `AlgebraicNumber`.** A raw non-owning
   pointer inside a copy-across-boundaries value type is a dangling/double-free
   hazard. If Phase 1/2 profiling justifies a cache, add a
   `std::shared_ptr<void>` (libpoly deleter) excluded from equality/hash —
   never a raw `void*`.

3. **No separate `Kind kind_` field in `RealValue`.** The
   `std::variant<mpq_class, AlgebraicNumber>` index is the single source of
   truth (avoids tag/payload desync); `kind()` derives from it.
