# NLColver — AI Agent Notes

## Project Overview

NLColver (**N**on**L**inear **Co**nstraint So**lver**) is a research-grade SMT/OMT solver platform with dual-engine architecture:
- **CDCL(T) / MCSAT** exact kernel for sound SAT/UNSAT reasoning
- **Local Search Advisor** for heuristic guidance and OMT optimization

Repository: `https://github.com/fuqi-jia/NLColver.git`

## Current Status

**Stages A–E functional, Stage I (NIA-Core) MVP complete.**

Core solvers (boolean, LRA, LIA, NRA) are functional. NIA-Core now has a working pipeline with sound conflict generation and model validation.

### What's Working

- ✅ CMake build system (C++17, GMP/MPFR, nlohmann/json, doctest)
- ✅ SOMTParser integration (git submodule, FrontendAdapter, Rewriter)
- ✅ SMT-LIB parsing: `nlcolver solve file.smt2`
- ✅ Internal IR: CoreExpr / CoreIr with scope-aware assertions
- ✅ Atomizer: Tseitin CNF conversion + theory atom extraction
- ✅ SAT backend: CaDiCaL wrapper + unit-propagation stub fallback
- ✅ Solver API: parseFile, checkSat, push/pop, dumpSMT2, seed option
- ✅ ModelValidator: boolean expression evaluator skeleton
- ✅ TraceRecorder + Statistics skeletons
- ✅ CLI subcommands: solve, bench, trace, model-check, proof-check, version
- ✅ CLI auto-detects `(set-logic ...)` from parsed SMT2 files

### Theory Solvers (functional)

| Stage | Component | Status | Coverage |
|-------|-----------|--------|----------|
| C/E | LraSolver (LRA) | ✅ MVP | Single-variable bound propagation, CDCL(T) loop |
| C/E | LiaSolver (LIA) | ✅ Phase 1 | Branch-and-bound, gcd-strength disequality, dynamic atom registry |
| D | NraSolver (NRA) | ✅ MVP | Grid sampling, univariate + bivariate polynomial constraints |
| I | NiaSolver (NIA-Core) | ✅ MVP | Univariate RRT, square rules, GCD conflict, modular reasoning, bounded enumeration, sound conflict generation |
| F | IncrementalLinearizer | 🏗️ Skeleton | Lemma generation interface ready |
| G | LocalSearchAdvisor | 🏗️ Skeleton | Model proposal interface ready |
| H | McsatSolver | 🏗️ Skeleton | MCSAT engine interface ready |
| J | ProofManager | 🏗️ Skeleton | SAT/theory proof tracking interface ready |
| K | Optimize (OMT) | 🏗️ Skeleton | Single-objective optimization interface ready |

### NIA-Core Pipeline

```
assertLit (effective relation via negateRelation)
    ↓
NiaNormalizer (clear denominators, strict → non-strict)
    ↓
Trivial constants (constant contradiction → Conflict)
    ↓
LinearNiaDomainReasoner (single-var linear bounds)
    ↓
UnivariateIntegerReasoner (RRT integer roots, square bounds)
    ↓
AlgebraicIntegerReasoner (square rules, GCD conflict, modular reasoning)
    ↓
Empty domain check → Conflict
    ↓
BoundedNiaSolver (direct enumeration over finite domains)
    ↓
NiaLocalSearch (heuristic candidate SAT finder)
    ↓
Branch lemma or Unknown
```

### Verified End-to-End Cases

| Logic | Input | Result |
|-------|-------|--------|
| QF_BOOL sat | `(and p q)` | **sat** |
| QF_BOOL unsat | `p ∧ ¬p` | **unsat** |
| QF_LRA sat | `x>0 ∧ x<10` | **sat** |
| QF_LRA unsat | `x>0 ∧ x<0` | **unsat** |
| QF_LRA + bool unsat | `(p ∨ x>0) ∧ (¬p ∨ x<0) ∧ (x=0)` | **unsat** |
| QF_LIA sat | `2x≤5 ∧ x≥0` | **sat** |
| QF_LIA unsat | `2x=1` (Int) | **unsat** |
| QF_LIA diseq | `x≠0 ∧ x≥0 ∧ x≤0` | **unsat** |
| QF_NRA sat | `x²>2 ∧ x<0` | **sat** |
| QF_NRA unsat | `x²>2 ∧ x²<1` | **unsat** |
| QF_NRA 2D sat | `x²+y²≤1` | **sat** |
| QF_NRA 2D unsat | `y=x² ∧ y<0` | **unsat** |
| QF_NIA sat | `x²=4` | **sat** |
| QF_NIA unsat | `x²=2` | **unsat** |
| QF_NIA sat | `0≤x≤10 ∧ x²=49` | **sat** |
| QF_NIA unsat | `0≤x≤10 ∧ x²=50` | **unsat** |
| QF_NIA unsat | `x²+y²=3` | **unsat** (modular) |
| QF_NIA sat | `0≤x≤3 ∧ 0≤y≤3 ∧ xy=6` | **sat** |

### Directory Layout

```
NLColver/
├── third_party/
│   ├── SOMTParser/          # Git submodule — SMT/OMT parser
│   ├── cadical/             # Git submodule — SAT backend
│   └── libpoly/             # Git submodule — polynomial kernel
├── include/nlcolver/        # Public C++ API
│   ├── Result.h
│   ├── Solver.h
│   ├── Sort.h
│   ├── Term.h
│   ├── Model.h
│   ├── Proof.h
│   └── Statistics.h
├── src/
│   ├── api/                 # C++ API implementation (Solver.cpp)
│   ├── parser/              # SOMTParser bridge (FrontendAdapter)
│   ├── expr/                # Core IR (types, payload, ir)
│   ├── sat/                 # SAT engine (CaDiCaL + stub) + Atomizer
│   ├── theory/              # Theory solvers
│   │   ├── TheorySolver.h
│   │   ├── TheoryManager.h/.cpp
│   │   ├── TheoryAtomRegistry.h/.cpp
│   │   ├── euf/             # (reserved)
│   │   └── arith/
│   │       ├── lra/SimplexSolver.h/.cpp
│   │       ├── lia/LiaSolver.h/.cpp
│   │       ├── nra/NraSolver.h/.cpp
│   │       ├── nia/         # NIA-Core engines
│   │       │   ├── NiaSolver.h/.cpp
│   │       │   ├── NiaNormalizer.h/.cpp
│   │       │   ├── DomainStore.h/.cpp
│   │       │   ├── UnivariateIntegerReasoner.h/.cpp
│   │       │   ├── LinearNiaDomainReasoner.h/.cpp
│   │       │   ├── AlgebraicIntegerReasoner.h/.cpp
│   │       │   ├── BoundedNiaSolver.h/.cpp
│   │       │   ├── NiaLocalSearch.h/.cpp
│   │       │   ├── IntegerModelValidator.h/.cpp
│   │       │   └── NiaTypes.h
│   │       ├── poly/        # PolynomialKernel, LibPolyKernel, PolynomialConverter
│   │       └── IncrementalLinearizer.h/.cpp
│   ├── mcsat/               # MCSAT/NLSAT engine
│   │   └── McsatSolver.h/.cpp
│   ├── search/              # Local search + strategy
│   │   └── LocalSearchAdvisor.h/.cpp
│   ├── omt/                 # Optimization
│   │   └── Optimize.h/.cpp
│   ├── proof/               # Proof/certificate infrastructure
│   │   └── ProofManager.h/.cpp
│   ├── learning/            # TraceRecorder + advisor interface
│   └── util/                # SmallVector, infrastructure
├── tests/
│   ├── fuzz/
│   ├── regression/
│   │   └── nia/             # NIA regression SMT2 files
│   ├── unit/                # doctest unit tests
│   └── CMakeLists.txt
├── tools/cli/               # nlcolver command-line
├── CMakeLists.txt
├── README.md
├── AGENTS.md                # This file
└── plan.md                  # Full Stage A–K design document
```

## Build Commands

```bash
# First time only
git submodule update --init --recursive

# Standard build
mkdir build && cd build
cmake ..                    # Release by default
cmake --build . -j$(nproc)
ctest
```

### Build Types

- Default `CMAKE_BUILD_TYPE` is `Release` (`-O3`).
- For debugging: `cmake -DCMAKE_BUILD_TYPE=Debug ..` (`-g -O0`).

## Build Options

| Option | Default | Description |
|--------|---------|-------------|
| `NLCOLVER_BUILD_TESTS` | ON | Build unit tests and regression suite |
| `NLCOLVER_BUILD_TOOLS` | ON | Build CLI tools |
| `NLCOLVER_ENABLE_PROOFS` | ON | Enable proof production infrastructure |
| `NLCOLVER_ENABLE_TRACING` | ON | Enable trace/recording for learning |

## Dependencies

| Package | Required | Notes |
|---------|----------|-------|
| GMP | ✅ | `libgmp-dev` |
| MPFR | ✅ | `libmpfr-dev` |
| CaDiCaL | ✅ (vendored) | `third_party/cadical` — SAT backend |
| libpoly | ✅ (vendored) | `third_party/libpoly` — polynomial kernel |
| nlohmann/json | ✅ (FetchContent) | JSON handling |
| doctest | ✅ (FetchContent) | Unit testing |

### Dependency Handling (Silent Degradation)

The CMake config has **silent degradation**: `cmake ..` will succeed even when SAT or polynomial backends are missing. It emits `WARNING` messages and stubs the backends out via compile-definition flags.

| Dependency | Found via | If missing |
|---|---|---|
| GMP, MPFR | pkg-config / `find_library` | **FATAL_ERROR** |
| CaDiCaL | `configure` + `make` in submodule dir | Warning + `NLCOLVER_HAS_CADICAL` undefined → SAT backend stubbed |
| libpoly | `add_subdirectory` | Warning + `NLCOLVER_HAS_LIBPOLY` undefined → polynomial kernel stubbed |
| nlohmann/json v3.11.3 | FetchContent (network) | Build fails |
| doctest v2.4.11 | FetchContent (network) | Tests skip |

When wiring code into `sat/` or `poly/`, gate it behind `#ifdef NLCOLVER_HAS_CADICAL` / `#NLCOLVER_HAS_LIBPOLY` and provide a stub fallback.

## Code Style Guidelines

- **C++17 minimum.** `set(CMAKE_CXX_STANDARD 17)`, extensions OFF. No GCC-isms.
- **Namespace:** All library code lives in `namespace nlcolver { ... }`.
- **Typed IDs:** Use `uint32_t` IDs for everything hash-consed: `ExprId`, `SortId`, `VarId`, `AtomId`, `PolyId`, `ClauseId`, `ProofId`. Each has a `NullX` sentinel in `src/expr/types.h`. Do not introduce parallel ID schemes.
- **pImpl pattern:** Used at the public-API boundary (`Solver::Impl`). Keep heavy includes (libpoly, CaDiCaL) out of `include/nlcolver/`.
- **Includes:**
  - Public headers use `<nlcolver/...>`.
  - Internal headers use relative paths.
- **Containers:** `SmallVector<T, 4>` (in `src/util/SmallVector.h`) is the default container for short child-lists on `CoreExpr` nodes. Use it instead of `std::vector` where N is typically small.
- **Compiler flags:** `-Wall -Wextra -Wpedantic -Wno-unused-parameter` applied **only** to `nlcolver_core`, not vendor code. Do not suppress other warnings — fix the root cause.
- **CMake file discovery:** `src/CMakeLists.txt` uses `file(GLOB_RECURSE ... CONFIGURE_DEPENDS)` over each subsystem directory. New `.cpp`/`.h` files under `src/<subsystem>/` are picked up automatically — no need to edit CMakeLists.

## Testing Instructions

### Framework

Tests use **doctest** v2.4.11 (header-only, fetched via FetchContent).

- `tests/unit/test_main.cpp` defines `DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN`.
- All other unit test files include `<doctest/doctest.h>` and declare `TEST_CASE` macros.
- Common pattern: write temporary `.smt2` files to `std::filesystem::temp_directory_path()` for end-to-end tests.

### Running Tests

```bash
# All tests
ctest

# Unit tests only
ctest -R unit

# Run unit test binary directly
./build/tests/nlcolver_unit_tests

# Single test case
./build/tests/nlcolver_unit_tests --test-case="NIA-Core: x^2 = 4 -> sat"

# List all test cases
./build/tests/nlcolver_unit_tests -ltc
```

### Manual CLI Tests

```bash
./build/bin/nlcolver solve tests/unit/test_bool.smt2
./build/bin/nlcolver solve tests/regression/nia/nia_001_sat_x2_eq_4.smt2
./build/bin/nlcolver solve tests/regression/nia/nia_002_unsat_x2_eq_2.smt2
```

## Architecture Invariants

1. **Soundness boundary.** `Result::Sat` must be backed by a `ModelValidator` pass over original assertions. Local search, MCSAT value proposals, and bit-blasted NIA results are all *candidates only* — they must be validated by the exact kernel before being returned. Never short-circuit this.

2. **Advisor pattern for anything heuristic.** Local search, learning modules, portfolio schedulers — all flow through `Advisor::propose() → Proposal → policy.accept()`. Heuristics never write solver state directly.

3. **Three views of an expression, kept separately.**
   - **DAG view** (`Expr` in `src/expr/`): for rewriting, proof, pretty-printing. Hash-consed; never mutate.
   - **Polynomial view** (`PolyId` in `src/theory/arith/poly/`): for theory reasoning. Canonical sparse polynomial via libpoly.
   - **Evaluation view**: for local-search incremental scoring.

4. **Atomizer separates SAT literals from theory atoms.** A theory atom (`AtomId`, theory + poly + relation) is *not* a SAT variable; the abstraction `b_i ↔ atom_i` is managed by the Atomizer, not implicit.

5. **CDCL(T) is the main loop; MCSAT is parallel research path.** Theory solvers implement two interfaces (`TheorySolver` for CDCL(T) and `McsatSolver` for trail-based reasoning). Don't merge them.

6. **Rewriter is DAG-safe and memoized.** Bottom-up with a memo table; optional fixpoint. A naive recursive rewrite blows up on shared subterms.

7. **NIA soundness over completeness.** NIA is undecidable. SAT requires exact integer validation. UNSAT requires sound proof (constant contradiction, empty roots, modular contradiction, GCD contradiction, or finite-domain exhaustion). Unknown is acceptable for unbounded cases. Never emit UNSAT from incomplete reasoning.

## Security Considerations

- Public repository on GitHub — no secrets, credentials, or proprietary data.
- No CI/CD pipeline configured yet.

## Notes for Agents

1. **plan.md is the canonical design document.** Read it before making architectural decisions. It contains the full Stage A–K roadmap with interfaces, data structures, and acceptance criteria.

2. **CLAUDE.md contains additional technical guidance.** It documents subsystem mappings to `plan.md` sections, key files for NIA work, and reference solver usage. Read it alongside this file.

3. **SOMTParser is a git submodule.** If it appears empty, run `git submodule update --init --recursive`.

4. **CaDiCaL and libpoly are vendored submodules.** The build system builds them automatically and defines `NLCOLVER_HAS_CADICAL` / `NLCOLVER_HAS_LIBPOLY` macros.

5. **Directory structure is intentionally flat.** `theory/arith/` aggregates all arithmetic; `search/` aggregates local search + strategy; `expr/` aggregates core IR. Do not reintroduce fine-grained top-level directories.

6. **SOMTParser already provides hash-consing, rewriter, visitor.** Do not reimplement these. The internal CoreIr is a lightweight dense array for solver-specific metadata (literal IDs, proof IDs, scope levels), not a replacement for SOMTParser's DAG.

7. **TheoryManager dispatches to all registered solvers.** Each solver silently ignores unsupported constraints. For MVP, positive theory literals are asserted; negative literals are handled by SAT-level negation.

8. **CLI auto-detects logic from `(set-logic ...)` in SMT2 files.** If no logic is set, default is LRA path, which will mark nonlinear constraints as unsupported and return Unknown.

9. **The `implementation_process/` directory** contains historical design documents and chat logs from the iterative development process. It is not source code and can be ignored for builds, but may contain useful context for understanding design decisions.
