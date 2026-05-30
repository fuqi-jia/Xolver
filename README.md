# Xolver

Xolver is an SMT solver for quantifier-free nonlinear arithmetic and its
combinations with uninterpreted functions, arrays, and algebraic datatypes. A
CaDiCaL-driven CDCL(T) core orchestrates theory solvers that reason over exact
rational (GMP/MPFR) and real-algebraic (libpoly) arithmetic, with no floating
point on the decision path. Incomplete reasoning yields `unknown` rather than
an unsound verdict.

Xolver was submitted as a Standalone solver to **SMT-COMP 2026** in the
QF\_NonLinearIntArith, QF\_NonLinearRealArith, and QF\_Equality+NonLinearArith
divisions.

---

## Highlights

- **Sound by construction.** Every `sat` is replayed through a `ModelValidator`
  over the original assertions; every `unsat` is backed by an explicit proof
  (constant contradiction, empty root set, GCD/modular contradiction, or a
  projection-certified covering). Heuristic methods only propose — never decide.
- **Exact arithmetic throughout.** Rational (GMP/MPFR) and real-algebraic
  (libpoly) kernels; no floating point in the decision path.
- **Nonlinear real arithmetic.** An effort ladder of exact linear/sign
  presolve → incremental linearization → complete CDCAC (cylindrical algebraic
  coverings) with selectable Collins or Lazard projection.
- **Nonlinear integer arithmetic.** Univariate RRT + algebraic reasoning (square
  rules, GCD, modular contradictions) + bounded enumeration + a bit-blasting
  backend + an integer-aware CDCAC over the real relaxation.
- **Combination & arrays.** Congruence closure over an e-graph with proof
  forest; lazy read-over-write + extensionality for arrays; algebraic datatypes
  via a lazy constructor/selector plugin; Nelson–Oppen exchange in combined
  logics.
- **Differentially tested** against z3 and cvc5 over the per-logic regression
  corpora.

---

## Supported logics

| Family | Logics |
|---|---|
| Boolean / EUF | `QF_BOOL`, `QF_UF` |
| Linear real / integer | `QF_LRA`, `QF_LIA`, `QF_LIRA` |
| Difference logic | `QF_IDL`, `QF_RDL` |
| Nonlinear | `QF_NRA`, `QF_NIA`, `QF_NIRA` |
| UF + arithmetic | `QF_UFLRA`, `QF_UFLIA`, `QF_UFNRA`, `QF_UFNIA` |
| Arrays (+arith, +UF) | `QF_AX`, `QF_ALIA`, `QF_ALRA`, `QF_AUFLIA`, `QF_AUFLRA`, `QF_ANIA`, `QF_AUFNIA` |
| Datatypes | `QF_DT`, `QF_UFDT`, `QF_UFDTNIA` |

---

## Architecture

```
            SMT-LIB 2 input
                  │
            SOMTParser  (frontend, git submodule)
                  │
        Frontend lowering worklist
   (ToInt / div-mod / ITE lowering, constant propagation)
                  │
   ┌──────────────┴───────────────────────────────┐
   │  Core IR (Expr / Sort)  — hash-consed DAG     │  three views of an
   │  Polynomial view (PolyId) — libpoly kernel    │  expression, kept
   │  Evaluation view — local-search scoring        │  separate
   └──────────────┬───────────────────────────────┘
                  │  Atomizer  (b_i ↔ theory atom_i)
                  │
            CaDiCaL SAT engine  (CDCL boolean core)
                  │  CDCL(T) main loop
                  ▼
        ┌─────────────────────────────────────────────┐
        │  Theory solvers (ArithSolverBase + Reasoner) │
        │   • LRA / LIA      simplex + branch&bound     │
        │   • IDL / RDL      Bellman–Ford difference    │
        │   • NRA            CDCAC + presolve fixpoint   │
        │   • NIA            NIA-Core + bit-blast        │
        │   • NIRA / LIRA    mixed int/real              │
        │   • EUF / Arrays   shared e-graph + lazy axioms│
        │   • Datatypes      lazy constructor plugin     │
        └──────────────────────┬──────────────────────┘
                  │  candidate models / conflicts
                  ▼
        ModelValidator (exact)        Advisor (heuristic, propose-only)
        — gates every `sat`           — local search, learning, portfolio
```

### Five stable seams

**User**, **Theory**, **Polynomial**, **Advisor**, **Certificate** — the five
APIs the system is built around. Subsystems follow their data structures and
invariants; nothing crosses these seams informally.

### Non-negotiable soundness invariants

1. `Result::Sat` must pass `ModelValidator` over the original assertions —
   local-search / bit-blasted / MCSAT results are *candidates only*.
2. Anything heuristic flows through `Advisor::propose() → policy.accept()`;
   heuristics never write solver state directly.
3. Three expression views (DAG / polynomial / evaluation) are kept separate.
4. The Atomizer keeps SAT literals distinct from theory atoms.
5. CDCL(T) is the main loop; MCSAT is a parallel research path.
6. NIA favors soundness over completeness — `unknown` is acceptable, a wrong
   verdict is not.

All arithmetic theory solvers share `src/theory/arith/ArithSolverBase` and drive
a `Reasoner` pipeline (see `src/theory/arith/README.md`).

---

## Building

### Prerequisites
| Dependency | Role | If missing |
|---|---|---|
| CMake ≥ 3.16, C++17 compiler | build | required |
| GMP, MPFR | exact rational/float | fatal error |
| CaDiCaL | SAT backend | fatal error |
| libpoly | polynomial / algebraic kernel | warning → kernel stubbed |
| nlohmann/json, doctest | JSON, unit tests | fetched at configure time |

### Clone (with submodules)
```bash
git clone --recursive git@github.com:fuqi-jia/Xolver.git
cd Xolver
# if you cloned without --recursive:
git submodule update --init --recursive
```

### Configure & build
```bash
mkdir build && cd build
cmake ..                 # Release (-O3) by default
cmake --build . -j       # on WSL/low-RAM, prefer a bounded -j 2 to avoid OOM
```

The CLI binary is produced at `build/bin/xolver`.

### CMake options (defaults shown)
| Option | Default | Effect |
|---|---|---|
| `XOLVER_BUILD_TESTS` | ON | doctest unit suite + regression harness |
| `XOLVER_BUILD_TOOLS` | ON | CLI, trace-viewer, model-checker, proof-checker |
| `XOLVER_ENABLE_PROOFS` | ON | proof-production infrastructure + `proof-check` |
| `XOLVER_ENABLE_TRACING` | ON | execution tracing for the learning layer |
| `XOLVER_STATIC_BUILD` | OFF | fully static executable |

For asserts/debugging: `cmake -DCMAKE_BUILD_TYPE=Debug ..`.

---

## Usage

```bash
# Solve an SMT-LIB 2 file (prints sat / unsat / unknown)
./build/bin/xolver solve path/to/input.smt2

# Produce a model for sat instances
./build/bin/xolver solve --produce-models input.smt2

# Other commands
./build/bin/xolver model-check <model>   # validate a model against assertions
./build/bin/xolver proof-check <proof>   # check a proof certificate
./build/bin/xolver version
```

Useful options: `--logic QF_NRA`, `--produce-proofs`, `--seed <n>`,
`-v/--verbose`. Run `xolver` with no arguments for the full list.

---

## Testing

```bash
# Full CTest suite (unit + per-logic regression)
cd build && ctest

# Unit tests directly
./build/tests/xolver_unit_tests
./build/tests/xolver_unit_tests --test-case="<name>"
./build/tests/xolver_unit_tests -ltc          # list cases

# Per-logic regression against z3/cvc5 oracle
python3 tools/run_regression.py --root tests/regression \
        --solver build/bin/xolver --timeout 20 -j 2
```

The regression harness compares each verdict against z3/cvc5 and flags any
`MISMATCH` (a sound solver must produce **zero** sat↔unsat disagreements).

---

## Repository layout

| Path | Contents |
|---|---|
| `include/xolver/` | public API headers (`Solver.h`, …) |
| `src/expr/` | hash-consed Core IR, rewriter |
| `src/parser/` | SOMTParser adapter |
| `src/frontend/` | lowering passes, theory factory |
| `src/sat/` | CaDiCaL wrapper |
| `src/theory/core/` | TheoryManager, Nelson–Oppen combination |
| `src/theory/arith/` | `ArithSolverBase`, `Reasoner`, per-theory solvers |
| `src/theory/arith/nra/` | CDCAC engine, projection, Lazard tower |
| `src/theory/arith/nia/` | NIA-Core, bit-blast |
| `src/theory/arith/poly/` | libpoly polynomial kernel |
| `src/theory/{euf,array,datatype}/` | e-graph + lazy axioms |
| `tools/` | CLI, build/test/benchmark scripts |
| `tests/` | doctest unit suite + per-logic regression corpora |
| `third_party/SOMTParser` | frontend parser (git submodule) |
| `third_party/cadical` | SAT backend (git submodule) |
| `third_party/libpoly` | polynomial / algebraic kernel (git submodule) |

---

## Status

| Component | State |
|---|---|
| SMT-LIB frontend, lowering, atomizer | functional |
| CaDiCaL SAT integration, CDCL(T) loop | functional |
| LRA, LIA, IDL, RDL | functional |
| NRA — CDCAC + Collins/Lazard projection, presolve fixpoint | functional |
| NIA — RRT + algebraic + modular + bounded enumeration + bit-blast | functional |
| NIRA, LIRA | functional |
| EUF, arrays (read-over-write + extensionality) | functional |
| Datatypes (constructor/injectivity/selector/tester/acyclicity) | functional |
| Nelson–Oppen combination | functional |
| MCSAT, advisor (local search / learning), proof emission, OMT | research / skeleton |

---

## License

Xolver is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
The full third-party dependency manifest is in [`NOTICE`](NOTICE).

Xolver does not call, wrap, link, or include source code from any existing SMT
solver. Source comments that cite cvc5, z3, or other SMT solvers are
algorithmic attribution for published algorithms (Cylindrical Algebraic
Coverings, Lazard projection, Nelson–Oppen, etc.); the implementations are
independently written.

Xolver was developed with substantial assistance from AI coding agents (Claude
Opus 4.7 / Sonnet 4.6, ChatGPT 5.5, Kimi 2.6), under the direction of the
author.

### Submissions
- SMT-COMP 2026 — see release tag and submission archive on
  [Zenodo](https://zenodo.org/records/20426099).

### Citation
```bibtex
@software{xolver,
  title  = {Xolver: an SMT solver for nonlinear arithmetic},
  author = {Jia, Fuqi and contributors},
  year   = {2026},
  url    = {https://github.com/fuqi-jia/Xolver}
}
```
