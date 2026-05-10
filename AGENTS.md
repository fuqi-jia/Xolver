# NLColver — AI Agent Notes

## Project Overview

NLColver (**N**on**L**inear **Co**nstraint So**lver**) is a research-grade SMT/OMT solver platform with dual-engine architecture:
- **CDCL(T) / MCSAT** exact kernel for sound SAT/UNSAT reasoning
- **Local Search Advisor** for heuristic guidance and OMT optimization

Repository: `https://github.com/fuqi-jia/NLColver.git`

## Current Status

**Stages A–K skeleton complete.** Core solvers (boolean, LRA, NRA) are functional; remaining stages (F–K) have working skeletons ready for implementation.

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

### Theory Solvers (functional)

| Stage | Component | Status | Coverage |
|-------|-----------|--------|----------|
| C/E | LraSolver (LRA) | ✅ MVP | Single-variable bound propagation, CDCL(T) loop |
| C/E | LiaSolver (LIA) | ✅ Phase 1 | Branch-and-bound, gcd-strength disequality, dynamic atom registry |
| D | CdcacSolver (NRA) | ✅ MVP | Grid sampling, univariate + bivariate polynomial constraints |
| F | IncrementalLinearizer | 🏗️ Skeleton | Lemma generation interface ready |
| G | LocalSearchAdvisor | 🏗️ Skeleton | Model proposal interface ready |
| H | McsatSolver | 🏗️ Skeleton | MCSAT engine interface ready |
| I | NiaSolver | 🏗️ Skeleton | NIA hybrid interface ready |
| J | ProofManager | 🏗️ Skeleton | SAT/theory proof tracking interface ready |
| K | Optimize (OMT) | 🏗️ Skeleton | Single-objective optimization interface ready |

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
│   │   ├── euf/             # (reserved)
│   │   └── arith/
│   │       ├── lra/SimplexSolver.h/.cpp
│   │       ├── cad/CdcacSolver.h/.cpp
│   │       ├── nia/NiaSolver.h/.cpp
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
│   └── unit/                # doctest unit tests
├── tools/cli/               # nlcolver command-line
├── CMakeLists.txt
├── README.md
├── AGENTS.md                # This file
└── plan.md                  # Full Stage A–K design document
```

## Build Commands

```bash
mkdir build && cd build
cmake ..
cmake --build . -j$(nproc)
ctest
```

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

## Code Style Guidelines

- C++17 minimum.
- Follow SOMTParser conventions.
- Internal headers use relative paths; public headers use `<nlcolver/...>`.
- Target-specific compile options (`-Wall -Wextra -Wpedantic`) applied only to `nlcolver_core`, not vendor code.

## Testing Instructions

```bash
# Unit tests
ctest -R unit

# Manual CLI tests
./build/bin/nlcolver solve tests/unit/test_bool.smt2
./build/bin/nlcolver solve /tmp/test_lra.smt2
./build/bin/nlcolver solve /tmp/test_nra.smt2
```

## Security Considerations

- Public repository on GitHub — no secrets, credentials, or proprietary data.
- No CI/CD pipeline configured yet.

## Notes for Agents

1. **plan.md is the canonical design document.** Read it before making architectural decisions. It contains full Stage A–K roadmap with interfaces, data structures, and acceptance criteria.
2. **SOMTParser is a git submodule.** If it appears empty, run `git submodule update --init --recursive`.
3. **CaDiCaL and libpoly are vendored submodules.** The build system builds them automatically and defines `NLCOLVER_HAS_CADICAL` / `NLCOLVER_HAS_LIBPOLY` macros.
4. **Directory structure is intentionally flat.** `theory/arith/` aggregates all arithmetic; `search/` aggregates local search + strategy; `expr/` aggregates core IR. Do not reintroduce fine-grained top-level directories.
5. **SOMTParser already provides hash-consing, rewriter, visitor.** Do not reimplement these. The internal CoreIr is a lightweight dense array for solver-specific metadata (literal IDs, proof IDs, scope levels), not a replacement for SOMTParser's DAG.
6. **TheoryManager dispatches to all registered solvers.** Each solver silently ignores unsupported constraints. For MVP, positive theory literals are asserted; negative literals are handled by SAT-level negation.
