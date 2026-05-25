<!-- AGENTS.md for NLColver — maintained for AI coding agents. -->
<!-- Last updated: 2026-05-25 after full project exploration. -->

# NLColver — AI Agent Notes

## Project Overview

NLColver (**N**on**L**inear **Co**nstraint So**lver**) is a research-grade SMT/OMT solver platform with dual-engine architecture:
- **CDCL(T) / MCSAT** exact kernel for sound SAT/UNSAT reasoning
- **Local Search Advisor** for heuristic guidance and OMT optimization

Repository: `https://github.com/fuqi-jia/NLColver.git`

## Current Status

**Stages A–E functional, Stage I (NIA-Core) MVP complete. All 15 historical known-fails are closed.**

Core infrastructure (boolean, LRA, LIA, NRA, EUF, IDL, RDL) is operational. NIA-Core has a working pipeline with sound conflict generation and model validation. Stages F/G/H/J/K are skeleton interfaces only.

Current baseline (as of 2026-05-25): **ctest 15/15, unit tests ~523, regression 577/577 across 15 logics, 0 known fails, 0 unsound.**

### Theory Solvers (functional)

| Stage | Component | Status | Coverage |
|-------|-----------|--------|----------|
| A/E | LraSolver (LRA) | ✅ Functional | Single-variable bound propagation, CDCL(T) loop |
| A/E | LiaSolver (LIA) | ✅ Phase 1 | Branch-and-bound, GCD-strengthened disequality, dynamic atom registry |
| D | NraSolver (NRA) | ✅ MVP | CDCAC engine (covering, projection, reason management), grid sampling, univariate + bivariate polynomial constraints |
| I | NiaSolver (NIA-Core) | ✅ MVP | 15-stage reasoner pipeline: normalize → linear domain → square bounds → univariate RRT → algebraic (GCD/modular) → bounded enumeration → local search → branch |
| A–E | EufSolver (EUF) | ✅ Functional | Congruence closure, distinct constraints, boolean predicates, incremental E-graph |
| A–E | IdlSolver (IDL) | ✅ Functional | Integer difference logic, Bellman-Ford negative-cycle detection |
| A–E | RdlSolver (RDL) | ✅ Functional | Real difference logic, difference constraint graphs |
| B | PolynomialKernel | ✅ Functional | libpoly-backed canonical sparse polynomials |
| B | IntervalEvaluator | ✅ Functional | Polynomial interval arithmetic, ReasonedBox (Q / Z) |
| F | IncrementalLinearizer | 🏗️ Skeleton | Lemma generation interface; McCormick / square-cut / sign lemmas not yet wired |
| G | LocalSearchAdvisor | 🏗️ Skeleton | Model proposal interface ready |
| H | McsatSolver | 🏗️ Skeleton | MCSAT engine interface ready |
| J | ProofManager | 🏗️ Skeleton | SAT/theory proof tracking interface ready |
| K | Optimize (OMT) | 🏗️ Skeleton | Single-objective optimization interface ready |

### NIA-Core Pipeline (15 stages)

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
| QF_UF sat | `f(a)=b ∧ f(c)=d` | **sat** |
| QF_UF unsat | `a=b ∧ f(a)≠f(b)` | **unsat** |
| QF_IDL sat | `x−y≤3 ∧ y−z≤−1 ∧ z−x≤−2` | **sat** |
| QF_RDL sat | `x−y≤1.5 ∧ y−z≤2.0` | **sat** |

## Directory Layout

```
NLColver/
├── third_party/
│   ├── SOMTParser/          # Git submodule — SMT/OMT parser + typed DAG IR
│   ├── cadical/             # Git submodule — SAT backend (CaDiCaL)
│   └── libpoly/             # Git submodule — polynomial kernel (SRI)
├── include/nlcolver/        # Public C++ API headers (pImpl boundary)
│   ├── Result.h
│   ├── Solver.h
│   ├── Sort.h
│   ├── Term.h
│   ├── Model.h
│   ├── Proof.h
│   └── Statistics.h
├── src/
│   ├── api/                 # C++ API implementation (Solver.cpp)
│   ├── expr/                # Core IR (types, payload, ir, rewriter, dumper)
│   ├── frontend/            # Preprocessing + atomization + theory factory
│   │   ├── atomization/     # Tseitin CNF + theory atom extraction
│   │   ├── preprocess/      # Lowering/normalization passes
│   │   └── factory/         # Central solver factory (logic → solver set)
│   ├── parser/              # SOMTParser bridge (FrontendAdapter)
│   ├── sat/                 # SAT engine (CaDiCaL wrapper + propagator)
│   ├── theory/              # Theory solvers
│   │   ├── core/            # TheorySolver base, TheoryManager, atom registry
│   │   ├── combination/     # Nelson-Oppen combination (shared terms, equalities)
│   │   ├── euf/             # EUF solver (congruence closure, E-graph)
│   │   └── arith/           # All arithmetic + shared infrastructure
│   │       ├── lra/         # Simplex-based LRA solver
│   │       ├── lia/         # Branch-and-bound LIA solver
│   │       ├── nra/         # CDCAC NRA solver
│   │       ├── nia/         # NIA-Core (15-stage reasoner pipeline)
│   │       ├── nira/        # NIRA dispatcher (nonlinear int+real)
│   │       ├── lira/        # LIRA dispatcher (linear int+real)
│   │       ├── idl/         # Integer difference logic
│   │       ├── rdl/         # Real difference logic
│   │       ├── dl/          # Difference-logic shared data structures
│   │       ├── poly/        # LibPolyKernel, PolynomialConverter
│   │       ├── interval/    # Interval arithmetic & ReasonedBox (Q/Z)
│   │       ├── icp/         # Interval constraint propagation
│   │       ├── linear/      # Linear expression, normalizer, model validator
│   │       ├── linearizer/  # Incremental linearization skeleton
│   │       ├── presolve/    # Theory-check presolve engine
│   │       ├── integer/     # Shared integer reasoning
│   │       └── search/      # Candidate model search / finite-domain enumeration
│   ├── proof/               # Proof/certificate + ModelValidator + ArithModelValidator
│   ├── util/                # SmallVector, Statistics, RealValue, GMP helpers
│   └── experimental/        # Skeleton modules
│       ├── learning/        # TraceRecorder skeleton
│       ├── mcsat/           # MCSAT/NLSAT engine skeleton
│       ├── omt/             # Optimization skeleton
│       └── search/          # Local search advisor skeleton
├── tests/
│   ├── fuzz/                # Empty placeholder
│   ├── regression/          # SMT-LIB 2 regression files (15 logics)
│   │   ├── bool/ euf/ idl/ lia/ lira/ lra/ nia/ nira/ nra/ rdl/
│   │   └── uflia/ uflra/ ufnia/ ufnra/
│   ├── unit/                # doctest unit tests (~52 C++ files)
│   └── CMakeLists.txt
├── tools/
│   ├── cli/                 # nlcolver command-line binary (main.cpp)
│   ├── run_benchmark.py     # Python benchmark runner (HTML reports, Z3 cross-check)
│   ├── run_regression.py    # Regression test runner (CTest-integrated)
│   ├── analyze_benchmark.py # Post-process benchmark results
│   ├── compare_benchmarks.py
│   ├── stamp_status.py      # Auto-stamp SMT2 files with :status
│   ├── freeze_baseline.py
│   └── ...
├── benchmark/               # Benchmark dataset directory (gitignored)
├── benchmark_results/       # Generated benchmark outputs (gitignored)
├── reference/               # cvc5/ and z3/ source copies for reading only (gitignored)
├── implementation_process/  # Historical design docs & chat logs
│   └── 1.plan.md            # Canonical master design document (Chinese)
├── CMakeLists.txt
├── README.md
├── CLAUDE.md                # Additional technical guidance for Claude Code
├── milestone-2026-05-13.md  # Latest milestone snapshot (Chinese)
└── AGENTS.md                # This file
```

## Build System

CMake 3.16+, C++20 (standard required, extensions OFF). Default build type is `Release` (`-O3`).

### Build Commands

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
- Multiple specialized build directories exist in the tree:
  - `build/` — primary Release build
  - `build_asan/` — AddressSanitizer build
  - `build_debug_info/` — debug-info build
  - `build_profile/` — profiling build
  - `build_static/` — static linking build
  - `build_rebuild/` — clean rebuild staging

> **WSL build note:** `cmake --build . -j` (unlimited parallelism) can OOM and crash WSL on this tree. Use a bounded `-j 2` there.

### Build Options

| Option | Default | Description |
|--------|---------|-------------|
| `NLCOLVER_BUILD_TESTS` | ON | Build unit tests and regression suite |
| `NLCOLVER_BUILD_TOOLS` | ON | Build CLI tools |
| `NLCOLVER_ENABLE_PROOFS` | ON | Enable proof production infrastructure |
| `NLCOLVER_ENABLE_TRACING` | ON | Enable trace/recording for learning |
| `NLCOLVER_ENABLE_LRA_PROFILE` | OFF | LRA solver profiling |
| `NLCOLVER_ENABLE_LIA_PROFILE` | OFF | LIA solver profiling |
| `NLCOLVER_ENABLE_CASESTATS` | OFF | Per-case statistics collection |
| `NLCOLVER_BUILD_LIBPOLY_TESTS` | OFF | Build libpoly's own tests (slower) |
| `NLCOLVER_STATIC_BUILD` | OFF | Static linking (`-static -pthread`) |

### Automatic File Discovery

`src/CMakeLists.txt` uses `file(GLOB_RECURSE ... CONFIGURE_DEPENDS)` over each subsystem directory. **New `.cpp`/`.h` files under `src/<subsystem>/` are picked up automatically** — no need to edit CMakeLists.

## Dependencies

| Package | Required | Integration | Notes |
|---------|----------|-------------|-------|
| GMP | ✅ | System (pkg-config / `find_library`) | `libgmp-dev`. Fatal if missing. |
| MPFR | ✅ | System (pkg-config / `find_library`) | `libmpfr-dev`. Fatal if missing. |
| CaDiCaL | ✅ | Vendored submodule (`ExternalProject_Add`) | `third_party/cadical`. `./configure -O && make`. Fatal if missing. |
| libpoly | ✅ (soft) | Vendored submodule (`add_subdirectory`) | `third_party/libpoly`. Warning if missing; polynomial kernel stubs available. |
| SOMTParser | ✅ | Vendored submodule (`add_subdirectory`) | `third_party/SOMTParser`. Fatal if missing. |
| nlohmann/json | ✅ | FetchContent (GitHub) | v3.11.3. Fatal if network unavailable. |
| doctest | ✅ (for tests) | FetchContent (GitHub) | v2.4.11. Tests skip if unavailable. |

When wiring code into `poly/`, gate it behind `#ifdef NLCOLVER_HAS_LIBPOLY` and provide a stub fallback.

Compiler flags (`-Wall -Wextra -Wpedantic -Wno-unused-parameter`) are applied **only** to `nlcolver_core`, not vendor code. Do not suppress other warnings — fix the root cause.

## Code Style Guidelines

- **C++20 minimum.** `set(CMAKE_CXX_STANDARD 20)`, extensions OFF. No GCC-isms.
- **Namespace:** All library code lives in `namespace nlcolver { ... }`.
- **Typed IDs:** Use `uint32_t` IDs for everything hash-consed: `ExprId`, `SortId`, `VarId`, `AtomId`, `PolyId`, `ClauseId`, `ProofId`. Each has a `NullX` sentinel in `src/expr/types.h`. Do not introduce parallel ID schemes.
- **pImpl pattern:** Used at the public-API boundary (`Solver::Impl`). Keep heavy includes (libpoly, CaDiCaL) out of `include/nlcolver/`.
- **Includes:**
  - Public headers use `<nlcolver/...>`.
  - Internal headers use relative paths.
- **Containers:** `SmallVector<T, 4>` (in `src/util/SmallVector.h`) is the default container for short child-lists on `CoreExpr` nodes. Use it instead of `std::vector` where N is typically small.

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

8. **Arithmetic solver unification.** All 8 arithmetic solvers (LRA, LIA, NRA, NIA, NIRA, LIRA, IDL, RDL) share `ArithSolverBase` + `Reasoner` pipeline.
   - `ArithSolverBase` owns `state_.trail`, scope counters, and pending slot. `push`/`pop`/`backtrack`/`reset` are **finalized**; subclasses customize via `onAssertLit` / `onBacktrack` / `onReset` / `onPush` / `onPop` hooks.
   - `check()` is a `Reasoner` pipeline. `Reasoner::run()` returns `std::optional<TheoryCheckResult>`: `nullopt` = continue; value = stop with verdict. Register stages in the solver constructor using `CallbackReasoner`. A reasoner must never mutate `state_.trail`.

9. **Per-theory directory convention.** Each theory subdirectory follows this layout where applicable:
   - `<Theory>Solver.{h,cpp}` — facade, lifecycle hooks, reasoner registration
   - `core/` — data types (domain store, atom records)
   - `preprocess/` — theory-specific normalizers
   - `reasoners/` — `Reasoner`-shaped engines
   - `engine/` — low-level non-reasoner engines (e.g. CDCAC internals)
   - `backend/` — external-library shims (e.g. libpoly binding)

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

### Regression Tests

578 SMT-LIB 2 files across 15 logics (`bool`, `euf`, `idl`, `lia`, `lira`, `lra`, `nia`, `nira`, `nra`, `rdl`, `uflia`, `uflra`, `ufnia`, `ufnra`).

Each `.smt2` file contains `(set-info :status sat|unsat|unknown)` as the oracle. The regression runner (`tools/run_regression.py`) is CTest-integrated; each logic gets its own CTest entry and label.

```bash
# All regression tests
ctest -L regression

# Specific logic
ctest -L nia
ctest -L nra
```

**Verdicts:** `PASS`, `KNOWN_FAIL`, `UNEXPECTED_FAIL`, `UNSOUND`, `ERROR`, `TIMEOUT`.

**Known failures** are tracked in `tests/regression/KNOWN_FAILURES.md`. Two categories:
- `known-fail`: expected gap (solver returns `unknown` but oracle has an answer)
- `known-unsound`: confirmed soundness bug (solver returns opposite of oracle)

When a bug is fixed, **delete the corresponding line** from `KNOWN_FAILURES.md`.

### Manual CLI Tests

```bash
# Explicit solve subcommand
./build/bin/nlcolver solve tests/regression/nia/nia_001_sat_x2_eq_4.smt2
./build/bin/nlcolver solve tests/regression/nia/nia_002_unsat_x2_eq_2.smt2
./build/bin/nlcolver solve tests/regression/euf/euf_001_sat_basic_eq.smt2

# Default mode (no subcommand)
./build/bin/nlcolver tests/regression/nia/nia_001_sat_x2_eq_4.smt2
```

### Benchmark Runner

A Python 3 script is provided for SMT-LIB benchmark evaluation:

```bash
python tools/run_benchmark.py --logic QF_NIA -j 8 -t 30
python tools/run_benchmark.py --logic QF_LRA -j 8 -t 30 --compare-with z3
```

Outputs `summary.txt`, `results.csv`, `report.html`, `discrepancies.txt`, `errors.txt`, `statistics.json`, and `top_slow.txt` under `benchmark_results/<logic>_<timestamp>/`.

## CI/CD

**No CI/CD pipelines are currently configured.** There is no `.github/workflows/`. The only content under `.github/` is a prompt template for AI-assisted subsystem implementation.

## Deployment

The project produces a standalone CLI binary (`nlcolver`). A pre-built binary is occasionally kept in `bin/nlcolver` and packaged as `nlcolver-dist.tar.gz`. The `tools/deploy_and_run.sh` script supports remote execution. `run_euf_validation.sh` runs cross-logic benchmark validation with Z3 comparison.

## Security Considerations

- Public repository on GitHub — no secrets, credentials, or proprietary data.
- No CI/CD pipeline configured yet.
- `reference/cvc5/` and `reference/z3/` contain upstream source copies for reading only; they are not linked into the build and must not be copied into NLColver source.

## Notes for Agents

1. **`implementation_process/1.plan.md` is the canonical design document.** It contains the full Stage A–K roadmap (in Chinese) with interfaces, data structures, and acceptance criteria. Read it before making architectural decisions.

2. **`milestone-2026-05-13.md` is the latest status snapshot.** It records the current implementation state, verified cases, skeleton modules, and a prioritized TODO list (in Chinese).

3. **`CLAUDE.md` contains additional technical guidance.** It documents subsystem mappings to `plan.md` sections, key files for NIA work, and reference solver usage. Read it alongside this file.

4. **SOMTParser is a git submodule.** If it appears empty, run `git submodule update --init --recursive`.

5. **CaDiCaL and libpoly are vendored submodules.** The build system builds them automatically and defines `NLCOLVER_HAS_CADICAL` / `NLCOLVER_HAS_LIBPOLY` macros.

6. **Directory structure is intentionally flat.** `theory/arith/` aggregates all arithmetic; `search/` aggregates local search + strategy; `expr/` aggregates core IR. Do not reintroduce fine-grained top-level directories.

7. **SOMTParser already provides hash-consing, rewriter, visitor.** Do not reimplement these. The internal CoreIr is a lightweight dense array for solver-specific metadata (literal IDs, proof IDs, scope levels), not a replacement for SOMTParser's DAG.

8. **TheoryManager dispatches to all registered solvers.** Each solver silently ignores unsupported constraints. For MVP, positive theory literals are asserted; negative literals are handled by SAT-level negation.

9. **CLI auto-detects logic from `(set-logic ...)` in SMT2 files.** If no logic is set, the default path may mark nonlinear constraints as unsupported and return Unknown.

10. **The `implementation_process/` directory** contains historical design documents and chat logs from the iterative development process. It is not source code and can be ignored for builds, but may contain useful context for understanding design decisions.

11. **Do not silently take shortcuts or simplifications.** When a planned feature (e.g., tower reduction, algebraic-coefficient root isolation, exact zero detection) requires infrastructure that does not yet exist, **ask the user** instead of silently degrading to a weaker approximation. Soundness bugs are far more costly than a delay for clarification. Never replace a missing primitive with a "close enough" workaround without explicit approval.
