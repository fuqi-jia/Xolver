# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project context

NLColver is a research-grade SMT/OMT solver platform for nonlinear arithmetic. The repository is in **Stage A (bootstrap)** — the CMake build, top-level API headers (`include/solver/Solver.h`, `Result.h`), the `core/` IR skeleton (`Expr`, `Sort`, `Types`, `SmallVector`), and the directory scaffolding for all 16 planned subsystems exist, but most `src/<subsystem>/` directories contain no `.cpp` files yet. CLI tools (`tools/solver-cli`, etc.) are placeholder `main.cpp`s.

The frontend is **SOMTParser**, vendored as a git submodule at `third_party/SOMTParser`. After cloning, run `git submodule update --init --recursive` before building.

## The plan is the source of truth

`plan.md` (Chinese, ~2200 lines) is the architectural master document. It defines:
- The five stable APIs: User / Theory / Polynomial / Advisor / Certificate.
- The CDCL(T) + CAlC/CAC main path, MCSAT/NLSAT secondary path, and how incremental linearization bridges them.
- The 11 development stages (A → K), each with concrete acceptance criteria.

**Before adding any subsystem, read the corresponding section of `plan.md` and follow its data structures and invariants.** The README's architecture diagram is a thumbnail of plan.md §0; `AGENTS.md` is **stale** (it was written before the source skeleton was added — do not rely on its "no source code" claim).

## Build, test, run

```bash
# First time only
git submodule update --init --recursive

# Standard build
mkdir build && cd build
cmake ..                    # Release by default
cmake --build . -j

# Single test executable, doctest-based
ctest                       # all tests
./tests/nlcolver_unit_tests                          # all units, direct
./tests/nlcolver_unit_tests --test-case="<name>"     # single test
./tests/nlcolver_unit_tests -ltc                     # list test cases

# CLI
./bin/nlcolver path/to/input.smt2
```

CMake build options (defaults shown):

| Option | Default | Effect |
|---|---|---|
| `NLCOLVER_BUILD_TESTS` | ON | Enable doctest unit tests |
| `NLCOLVER_BUILD_TOOLS` | ON | Build `nlcolver-cli`, trace-viewer, benchmark-runner, model-checker, proof-checker |
| `NLCOLVER_ENABLE_PROOFS` | ON | Defines `NLCOLVER_ENABLE_PROOFS`, builds `proof-checker` tool |
| `NLCOLVER_ENABLE_TRACING` | ON | Defines `NLCOLVER_ENABLE_TRACING`, builds `trace-viewer` tool |

Default `CMAKE_BUILD_TYPE` is `Release` (`-O3`). For asserts/debugging use `cmake -DCMAKE_BUILD_TYPE=Debug ..` (`-g -O0`).

## Dependency tiers — read CMake output, not just exit code

The CMake config has **silent degradation**: `cmake ..` will succeed even when SAT or polynomial backends are missing. It only emits `WARNING` messages and stubs the backends out via the `NLCOLVER_HAS_CADICAL` / `NLCOLVER_HAS_LIBPOLY` compile-definition flags.

| Dependency | Found via | If missing |
|---|---|---|
| GMP, MPFR | pkg-config / `find_library` | **FATAL_ERROR** |
| CaDiCaL (SAT, headers expose `cadical.hpp`) | `find_library`/`find_path` | Warning + `NLCOLVER_HAS_CADICAL` undefined → SAT backend stubbed |
| libpoly (`poly/poly.h`) | `find_library`/`find_path` | Warning + `NLCOLVER_HAS_LIBPOLY` undefined → polynomial kernel stubbed |
| nlohmann/json v3.11.3 | FetchContent (network) | Build fails |
| doctest v2.4.11 | FetchContent (network) | Tests skip |

When wiring code into `sat/` or `poly/`, gate it behind `#ifdef NLCOLVER_HAS_CADICAL` / `NLCOLVER_HAS_LIBPOLY` and provide a stub fallback — the CMakeLists deliberately permits builds without them so Stage-A IR work isn't blocked.

`src/CMakeLists.txt` uses `file(GLOB_RECURSE ... CONFIGURE_DEPENDS)` over each subsystem directory: new `.cpp`/`.h` files under `src/<subsystem>/` are picked up automatically — no need to edit any CMakeLists.

## Architectural invariants (do not break)

These are non-negotiable per `plan.md` §0 and are easy to violate by accident:

1. **Soundness boundary.** `Result::Sat` must be backed by a `ModelValidator` pass over original assertions. Local search, MCSAT value proposals, and bit-blasted NIA results are all *candidates only* — they must be validated by the exact kernel before being returned. Never short-circuit this.

2. **Advisor pattern for anything heuristic.** Local search, learning modules (GNN/RL/LLM), portfolio schedulers — all of these flow through `Advisor::propose() → Proposal → policy.accept()`. Heuristics never write solver state directly. This is what protects soundness end-to-end.

3. **Three views of an expression, kept separately.**
   - **DAG view** (`Expr` in `src/core/Expr.h`): for rewriting, proof, pretty-printing. Hash-consed; never mutate.
   - **Polynomial view** (`PolyId` in the future `src/poly/`): for theory reasoning. Canonical sparse polynomial.
   - **Evaluation view**: for local-search incremental scoring.
   Don't force everything into the polynomial view eagerly — `plan.md` §2.3 calls this out specifically.

4. **Atomizer separates SAT literals from theory atoms.** A theory atom (`AtomId`, theory + poly + relation) is *not* a SAT variable; the abstraction `b_i ↔ atom_i` is managed by the AtomManager, not implicit. See `plan.md` §2.2.

5. **CDCL(T) is the main loop; MCSAT is parallel research path.** Theory solvers implement two interfaces (`TheorySolver` for CDCL(T) and `McsatSolver` for trail-based reasoning). Don't merge them — `plan.md` §5 explains why combination is harder under MCSAT.

6. **Rewriter is DAG-safe and memoized.** Bottom-up with a memo table; optional fixpoint. A naive recursive rewrite blows up on shared subterms.

## Code conventions observed in the existing skeleton

- `namespace nlcolver { ... }` for all library code.
- Typed `uint32_t` IDs for everything that is hash-consed: `ExprId`, `SortId`, `VarId`, `AtomId`, `PolyId`, `ClauseId`, `ProofId`. Each has a `NullX` sentinel in `src/core/Types.h`. Reuse these — don't introduce parallel ID schemes.
- `pImpl` pattern at the public-API boundary (`Solver::Impl`). Keep heavy includes (libpoly, CaDiCaL) out of `include/solver/`.
- C++17 only (`set(CMAKE_CXX_STANDARD 17)`, extensions OFF). No GCC-isms.
- Warnings on (`-Wall -Wextra -Wpedantic`); `-Wno-unused-parameter` is the only exception. Don't suppress others — fix the root cause.
- `SmallVector<T, 4>` (in `src/util/`) is the default container for short child-lists on `Expr` nodes. Use it instead of `std::vector` where N is typically small.

## Working on subsystems

The 16 `src/` subdirectories map 1:1 to sections of `plan.md`:

| Directory | plan.md section | Stage |
|---|---|---|
| `core/` | §2 (CoreExpr, Rewriter) | A |
| `frontend/` | §2 (SOMTParser adapter) | A |
| `preprocess/` | §6 | A–B |
| `sat/` | §4 (CaDiCaL wrapper) | A |
| `theory/` | §5 (TheoryManager, dual interfaces) | A onwards |
| `poly/` | §3 (PolynomialKernel, AlgebraicNumber) | B |
| `nra/` | §8, §9, §10 (CAlC/CAC, incremental linearization, MCSAT-NRA) | D, F, H |
| `nia/` | §12 (hybrid: LS + LIA + B&B + bit-blast) | I |
| `local_search/` | §11 (Advisor, never solver) | G |
| `omt/` | §14 | K |
| `proof/` | §15 | J |
| `learning/` | §16 (trace, advisor plugins) | continuous |
| `strategy/` | §17 (tactic pipeline, portfolio) | continuous |

When implementing a stub, look up the section, copy the data-structure shapes (they're prescribed in detail), and check that subsystem's "verification criteria" (`plan.md` §21) for what must pass before claiming the stage done.

## Reference solvers

`reference/` contains in-tree copies of `cvc5/` and `z3/` for reading, **not** for linking — they are not in any CMake target. Use them when the plan references "cvc5 does X" or when researching how a known-good solver implemented a particular algorithm. Do not copy code; the licensing posture of NLColver vs. those projects has not been settled.
