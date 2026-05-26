# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project context

Zolver is a research-grade SMT/OMT solver platform for nonlinear arithmetic. The repository has progressed beyond initial bootstrap:

- **Stage A (Core IR + SAT)**: Complete — CoreExpr, CoreIr, CaDiCaL SAT backend, Atomizer, frontend lowering worklist (ToInt/div-mod/ITE lowering, constant propagation)
- **Stage C/E (LRA/LIA)**: Functional — Simplex-based LRA, branch-and-bound LIA with disequality
- **Stage D (NRA)**: Functional — CDCAC engine + theory-check presolve fixpoint (exact linear/sign reasoning)
- **Stage I (NIA-Core)**: Functional — univariate RRT, algebraic reasoning (square rules, GCD, modular), bounded enumeration, presolve fixpoint, sound conflict generation
- **Shared arith infrastructure**: `ArithSolverBase` + `Reasoner` pipeline (all 8 solvers); a theory-check presolve fixpoint (`theory/arith/presolve/`); validated candidate search + complete finite-domain enumeration (`theory/arith/search/`)
- **Stages F, G, H, J, K**: Skeleton interfaces exist, not yet functional

All 15 historical known-fails are closed; the regression suite is fully green
(see Build/test/run below).

The frontend is **SOMTParser**, vendored as a git submodule at `third_party/SOMTParser`. After cloning, run `git submodule update --init --recursive` before building.

## The plan is the source of truth

`plan.md` (Chinese, ~2200 lines) is the architectural master document. It defines:
- The five stable APIs: User / Theory / Polynomial / Advisor / Certificate.
- The CDCL(T) + CAlC/CAC main path, MCSAT/NLSAT secondary path, and how incremental linearization bridges them.
- The 11 development stages (A → K), each with concrete acceptance criteria.

**Before adding any subsystem, read the corresponding section of `plan.md` and follow its data structures and invariants.**

## Build, test, run

```bash
# First time only
git submodule update --init --recursive

# Standard build
mkdir build && cd build
cmake ..                    # Release by default
cmake --build . -j

# Tests — doctest unit suite (~523 cases) + 14 per-logic regression suites
ctest                       # all tests (unit + per-logic regression)
./tests/zolver_unit_tests                          # all units, direct
./tests/zolver_unit_tests --test-case="<name>"     # single test
./tests/zolver_unit_tests -ltc                     # list test cases

# Regression: 577 SMT2 cases vs z3+cvc5 oracle, KNOWN_FAILURES.md gates leniency
python3 tools/run_regression.py --root tests/regression --solver build/bin/zolver --timeout 20 -j 2

# CLI
./bin/zolver solve path/to/input.smt2
```

> **WSL build note:** `cmake --build . -j` (unlimited parallelism) can OOM and
> crash WSL on this tree. Use a bounded `-j 2` there.

Current baseline (main): **ctest 15/15, unit 523/523, regression 577/577, 0
KNOWN_FAIL, 0 UNSOUND.** All 15 historical known-fails are closed.

CMake build options (defaults shown):

| Option | Default | Effect |
|---|---|---|
| `ZOLVER_BUILD_TESTS` | ON | Enable doctest unit tests |
| `ZOLVER_BUILD_TOOLS` | ON | Build `zolver-cli`, trace-viewer, benchmark-runner, model-checker, proof-checker |
| `ZOLVER_ENABLE_PROOFS` | ON | Defines `ZOLVER_ENABLE_PROOFS`, builds `proof-checker` tool |
| `ZOLVER_ENABLE_TRACING` | ON | Defines `ZOLVER_ENABLE_TRACING`, builds `trace-viewer` tool |

Default `CMAKE_BUILD_TYPE` is `Release` (`-O3`). For asserts/debugging use `cmake -DCMAKE_BUILD_TYPE=Debug ..` (`-g -O0`).

## Dependency tiers — read CMake output, not just exit code

| Dependency | Found via | If missing |
|---|---|---|
| GMP, MPFR | pkg-config / `find_library` | **FATAL_ERROR** |
| CaDiCaL (SAT, headers expose `cadical.hpp`) | `find_library`/`find_path` | **FATAL_ERROR** |
| libpoly (`poly/poly.h`) | `find_library`/`find_path` | Warning + `ZOLVER_HAS_LIBPOLY` undefined → polynomial kernel stubbed |
| nlohmann/json v3.11.3 | FetchContent (network) | Build fails |
| doctest v2.4.11 | FetchContent (network) | Tests skip |

When wiring code into `poly/`, gate it behind `#ifdef ZOLVER_HAS_LIBPOLY` and provide a stub fallback.

`src/CMakeLists.txt` uses `file(GLOB_RECURSE ... CONFIGURE_DEPENDS)` over each subsystem directory: new `.cpp`/`.h` files under `src/<subsystem>/` are picked up automatically — no need to edit any CMakeLists.

## Architectural invariants (do not break)

These are non-negotiable per `plan.md` §0 and are easy to violate by accident:

1. **Soundness boundary.** `Result::Sat` must be backed by a `ModelValidator` pass over original assertions. Local search, MCSAT value proposals, and bit-blasted NIA results are all *candidates only* — they must be validated by the exact kernel before being returned. Never short-circuit this.

2. **Advisor pattern for anything heuristic.** Local search, learning modules (GNN/RL/LLM), portfolio schedulers — all of these flow through `Advisor::propose() → Proposal → policy.accept()`. Heuristics never write solver state directly. This is what protects soundness end-to-end.

3. **Three views of an expression, kept separately.**
   - **DAG view** (`Expr` in `src/expr/`): for rewriting, proof, pretty-printing. Hash-consed; never mutate.
   - **Polynomial view** (`PolyId` in `src/theory/arith/poly/`): for theory reasoning. Canonical sparse polynomial via libpoly.
   - **Evaluation view**: for local-search incremental scoring.
   Don't force everything into the polynomial view eagerly — `plan.md` §2.3 calls this out specifically.

4. **Atomizer separates SAT literals from theory atoms.** A theory atom (`AtomId`, theory + poly + relation) is *not* a SAT variable; the abstraction `b_i ↔ atom_i` is managed by the Atomizer, not implicit. See `plan.md` §2.2.

5. **CDCL(T) is the main loop; MCSAT is parallel research path.** Theory solvers implement two interfaces (`TheorySolver` for CDCL(T) and `McsatSolver` for trail-based reasoning). Don't merge them — `plan.md` §5 explains why combination is harder under MCSAT.

6. **Rewriter is DAG-safe and memoized.** Bottom-up with a memo table; optional fixpoint. A naive recursive rewrite blows up on shared subterms.

7. **NIA soundness over completeness.** NIA is undecidable. SAT requires exact integer validation. UNSAT requires sound proof (constant contradiction, empty roots, modular contradiction, GCD contradiction, or finite-domain exhaustion). Unknown is acceptable for unbounded cases. Never emit UNSAT from incomplete reasoning.

## Arithmetic solver architecture: `ArithSolverBase` + `Reasoner`

All 8 arithmetic theory solvers (LRA, LIA, NRA, NIA, NIRA, LIRA, IDL, RDL)
share a common base, `src/theory/arith/ArithSolverBase.{h,cpp}`. **Read
`src/theory/arith/README.md` before touching any arith solver.** Summary:

1. **`ArithSolverBase` owns the lifecycle.** `state_.trail`
   (`vector<ActiveAssignment>` of `{level, lit, atom, value}`), scope
   counters, `currentLevel`, and an optional level-tagged pending slot all
   live in the base. `push` / `pop` / `backtrackToLevel` / `reset` are
   **finalized**; subclasses customize via `onAssertLit` / `onBacktrack` /
   `onReset` / `onPush` / `onPop` hooks. `assertLit` is **virtual** — most
   solvers use the base default (dedup-by-satVar insert), but NIA overrides
   it (ActiveLiteralSet + opposite-polarity detection) and LRA/LIA/NRA
   override it to drive their own simplex/cursor trail. Do **not**
   reintroduce a per-solver `struct ActiveAssignment`; it was deduplicated
   from 5 copies into the base.

2. **`check()` is a `Reasoner` pipeline.** `src/theory/arith/Reasoner.h`
   defines a stage interface returning `std::optional<TheoryCheckResult>`:
   `nullopt` = continue to the next stage, a value = stop with that verdict
   (`Consistent` here means "consistent, stop" — **not** "continue"). The
   base `check()` drains any pending result, then walks `reasoners_` and
   returns the first non-`nullopt`. Populate `reasoners_` in the solver
   constructor; `CallbackReasoner` wraps a `std::function` so each stage can
   be a `this`-capturing lambda over a per-stage method (no subclass per
   stage). Decomposed today: NRA (2 stages), NIA (15), LRA (1), LIA (1).
   **A reasoner must never mutate `state_.trail`** (only `assertLit` does;
   a debug assertion enforces this).

3. **Per-theory directory convention.** `core/` (data types), `preprocess/`
   (normalizers, e.g. `nia/preprocess/NiaNormalizer`), `reasoners/`
   (Reasoner-shaped engines), `engine/` (low-level non-reasoner engines),
   `backend/` (external-lib shims). Cross-cutting linear utilities live in
   `theory/arith/linear/`, not in a single theory's directory.

## Code conventions observed in the existing source

- `namespace zolver { ... }` for all library code.
- Typed `uint32_t` IDs for everything that is hash-consed: `ExprId`, `SortId`, `VarId`, `AtomId`, `PolyId`, `ClauseId`, `ProofId`. Each has a `NullX` sentinel in `src/expr/types.h`. Reuse these — don't introduce parallel ID schemes.
- `pImpl` pattern at the public-API boundary (`Solver::Impl`). Keep heavy includes (libpoly, CaDiCaL) out of `include/zolver/`.
- C++17 only (`set(CMAKE_CXX_STANDARD 17)`, extensions OFF). No GCC-isms.
- Warnings on (`-Wall -Wextra -Wpedantic`); `-Wno-unused-parameter` is the only exception. Don't suppress others — fix the root cause.
- `SmallVector<T, 4>` (in `src/util/`) is the default container for short child-lists on `CoreExpr` nodes. Use it instead of `std::vector` where N is typically small.

## Working on subsystems

The `src/` subdirectories map to sections of `plan.md`:

All `theory/arith/<theory>/` solvers inherit `ArithSolverBase` and drive a
`Reasoner` pipeline (see the architecture section above).

| Directory | plan.md section | Stage | Status |
|---|---|---|---|
| `expr/` | §2 (CoreExpr, Rewriter) | A | ✅ Functional |
| `parser/` | §2 (SOMTParser adapter) | A | ✅ Functional |
| `sat/` | §4 (CaDiCaL wrapper) | A | ✅ Functional |
| `theory/arith/` | — (`ArithSolverBase`, `Reasoner`) | — | ✅ Shared base + pipeline |
| `theory/arith/lra/` | §5 (LRA) | C/E | ✅ Functional |
| `theory/arith/lia/` | §5 (LIA) | C/E | ✅ Functional |
| `theory/arith/nra/` | §8, §9, §10 (NRA) | D | ✅ CDCAC + presolve fixpoint |
| `theory/arith/nia/` | §12 (NIA) | I | ✅ NIA-Core + presolve fixpoint |
| `theory/arith/presolve/` | theory-check presolve (Caps. 1–11) | — | ✅ Functional |
| `theory/arith/search/` | finite-domain enum + validated candidate search | — | ✅ Functional |
| `theory/arith/poly/` | §3 (PolynomialKernel) | B | ✅ Functional |
| `frontend/preprocess/` | §2 (lowering passes) | A | ✅ Functional |
| `mcsat/` | §10 (MCSAT-NRA) | H | 🏗️ Skeleton |
| `search/` | §11 (Advisor) | G | 🏗️ Skeleton |
| `omt/` | §14 | K | 🏗️ Skeleton |
| `proof/` | §15 | J | 🏗️ Skeleton |
| `learning/` | §16 (trace, advisor plugins) | continuous | 🏗️ Skeleton |

When implementing a new subsystem or extending an existing one, look up the section, copy the data-structure shapes (they're prescribed in detail), and check that subsystem's "verification criteria" (`plan.md` §21) for what must pass before claiming the stage done.

## Key files for NIA work

Paths reflect the per-theory subdir convention; `NiaSolver`'s `check()` is a
15-stage `Reasoner` pipeline (`stagePending` … `stageBranch`) registered in
its constructor — add/reorder stages there, not by hand-editing a monolithic
`check()`.

| File | Purpose |
|---|---|
| `src/theory/arith/nia/NiaSolver.h/.cpp` | Facade — owns kernel, registers the 15 reasoner stages, delegates to engines |
| `src/theory/arith/nia/core/DomainStore.h/.cpp` | Per-variable integer domains (intervals, finite sets, exclusions) |
| `src/theory/arith/nia/reasoners/UnivariateIntegerReasoner.h/.cpp` | RRT-based integer root finding |
| `src/theory/arith/nia/core/LinearNiaDomainReasoner.h/.cpp` | Single-variable linear bound inference |
| `src/theory/arith/nia/reasoners/AlgebraicIntegerReasoner.h/.cpp` | Square rules, GCD conflict, modular reasoning |
| `src/theory/arith/nia/reasoners/BoundedNiaSolver.h/.cpp` | Finite-domain complete enumeration |
| `src/theory/arith/nia/preprocess/NiaNormalizer.h/.cpp` | Clear denominators, strict → non-strict (moved from `core/` in Phase 4) |
| `src/theory/arith/poly/LibPolyKernel.h/.cpp` | libpoly backend — polynomial operations |
| `src/theory/arith/poly/PolynomialConverter.h/.cpp` | CoreIr → PolyId conversion |

## Reference solvers

`reference/` contains in-tree copies of `cvc5/` and `z3/` for reading, **not** for linking — they are not in any CMake target. Use them when the plan references "cvc5 does X" or when researching how a known-good solver implemented a particular algorithm. Do not copy code; the licensing posture of Zolver vs. those projects has not been settled.
