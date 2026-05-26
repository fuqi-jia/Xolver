# Zolver

**Z**ero-human-written SMT s**olver** — a research-grade SMT/OMT solver for
(non)linear arithmetic in which **every line of code is written by AI agents**,
not humans. The name is the thesis: a complete, sound constraint solver grown
end-to-end by autonomous agents working against a fixed architectural plan.

Zolver targets the quantifier-free arithmetic, array, and uninterpreted-function
fragments of SMT-LIB, with a dual-engine design: an **exact CDCL(T) kernel** for
sound `sat`/`unsat` reasoning and a heuristic **advisor** layer (local search,
learning) that may only *propose* — never decide — so soundness is preserved
end-to-end.

---

## Highlights

- **Sound by construction.** Every `sat` is replayed through a `ModelValidator`
  over the original assertions; every `unsat` is backed by an explicit proof
  (constant contradiction, empty root set, GCD/modular contradiction, or a
  complete projection-certified covering). When reasoning is incomplete the
  answer is `unknown` — never a guess.
- **Exact arithmetic throughout.** Rational (GMP/MPFR) and real-algebraic
  (libpoly) kernels; no floating point in the decision path.
- **Nonlinear real arithmetic** via CDCAC (Cylindrical Algebraic Coverings) with
  a theory-check presolve fixpoint, plus an experimental exact-algebraic **Lazard
  tower** lifting path.
- **Nonlinear integer arithmetic** (undecidable in general) via NIA-Core:
  univariate real-root tightening, algebraic reasoning (square rules, GCD &
  modular contradictions), bounded complete enumeration, and a sound bit-blasting
  fallback.
- **Combination & arrays** on a shared EUF e-graph (Nelson–Oppen style) covering
  `QF_AX`, `QF_ALIA`, `QF_ALRA`, `QF_AUFLIA`, `QF_AUFLRA`.
- **Differentially tested** against z3 and cvc5 over hundreds of regression cases.

---

## Supported logics

| Family | Logics |
|---|---|
| Boolean / EUF | `QF_BOOL`, `QF_UF` |
| Linear real / integer | `QF_LRA`, `QF_LIA`, `QF_LIRA` |
| Difference logic | `QF_IDL`, `QF_RDL` |
| Nonlinear | `QF_NRA`, `QF_NIA`, `QF_NIRA` |
| UF + arithmetic | `QF_UFLRA`, `QF_UFLIA`, `QF_UFNRA`, `QF_UFNIA` |
| Arrays (+arith, +UF) | `QF_AX`, `QF_ALIA`, `QF_ALRA`, `QF_AUFLIA`, `QF_AUFLRA` |

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
   │  Core IR (Expr / Sort)  — hash-consed DAG     │  three separate views of an
   │  Polynomial view (PolyId) — libpoly kernel    │  expression, kept distinct:
   │  Evaluation view — local-search scoring        │  DAG / polynomial / eval
   └──────────────┬───────────────────────────────┘
                  │  Atomizer  (b_i ↔ theory atom_i)
                  │
            CaDiCaL SAT engine  (CDCL boolean core)
                  │  CDCL(T) main loop   ┌─ MCSAT/NLSAT (research path)
                  ▼                      ▼
        ┌─────────────────────────────────────────────┐
        │  Theory solvers (ArithSolverBase + Reasoner) │
        │   • LRA / LIA      simplex + branch&bound     │
        │   • IDL / RDL      Bellman–Ford difference    │
        │   • NRA            CDCAC + presolve fixpoint   │
        │   • NIA            NIA-Core + bit-blast        │
        │   • NIRA / LIRA    mixed int/real              │
        │   • Arrays / UF    shared EUF e-graph          │
        └──────────────────────┬──────────────────────┘
                  │  candidate models / conflicts
                  ▼
        ModelValidator (exact)        Advisor (heuristic, propose-only)
        — gates every `sat`           — local search, learning, portfolio
```

### The five stable APIs (`plan.md`)
**User**, **Theory**, **Polynomial**, **Advisor**, **Certificate** — the seams the
whole system is built around. `plan.md` (the architectural master document) is the
source of truth; subsystems follow its data structures and invariants.

### Non-negotiable soundness invariants
1. `Result::Sat` must pass `ModelValidator` over the original assertions —
   local-search / MCSAT / bit-blasted results are *candidates only*.
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

### Clone (with the parser submodule)
```bash
git clone --recursive git@github.com:fuqi-jia/zolver.git
cd zolver
# if you cloned without --recursive:
git submodule update --init --recursive
```

### Configure & build
```bash
mkdir build && cd build
cmake ..                 # Release (-O3) by default
cmake --build . -j       # on WSL/low-RAM, prefer a bounded -j 2 to avoid OOM
```

The CLI binary is produced at `build/bin/zolver`.

### CMake options (defaults shown)
| Option | Default | Effect |
|---|---|---|
| `ZOLVER_BUILD_TESTS` | ON | doctest unit suite + regression harness |
| `ZOLVER_BUILD_TOOLS` | ON | CLI, trace-viewer, model-checker, proof-checker |
| `ZOLVER_ENABLE_PROOFS` | ON | proof-production infrastructure + `proof-check` |
| `ZOLVER_ENABLE_TRACING` | ON | execution tracing for the learning layer |
| `ZOLVER_STATIC_BUILD` | OFF | fully static executable |

For asserts/debugging: `cmake -DCMAKE_BUILD_TYPE=Debug ..`.

---

## Usage

```bash
# Solve an SMT-LIB 2 file (prints sat / unsat / unknown)
./build/bin/zolver solve path/to/input.smt2

# Produce a model for sat instances
./build/bin/zolver solve --produce-models input.smt2

# Other commands
./build/bin/zolver model-check <model>   # validate a model against assertions
./build/bin/zolver proof-check <proof>   # check a proof certificate
./build/bin/zolver version
```

Useful options: `--logic QF_NRA`, `--produce-proofs`, `--seed <n>`,
`-v/--verbose`. Run `zolver` with no arguments for the full list.

### Experimental flags
- `ZOLVER_NRA_LAZARD_LIFT=1` (environment) — enables the exact-algebraic Lazard
  tower lift for genuine algebraic-tower CDCAC cells. **Default off**; the default
  projection path is Collins-style and the flag only *adds* certified isolations,
  never changing the baseline behavior.

---

## Testing

```bash
# Full CTest suite (unit + per-logic regression)
cd build && ctest

# Unit tests directly
./build/tests/zolver_unit_tests
./build/tests/zolver_unit_tests --test-case="<name>"
./build/tests/zolver_unit_tests -ltc          # list cases

# Differential regression vs z3 + cvc5 oracle
python3 tools/run_regression.py --root tests/regression \
        --solver build/bin/zolver --timeout 20 -j 2

# Large-corpus benchmark runs (deploy + compare-with z3)
./tools/deploy_and_run.sh build
./tools/deploy_and_run.sh package
./zolver-dist/tools/deploy_and_run.sh run nra,lra -j 200 -t 100 --compare-with z3
```

The regression harness compares each verdict against z3/cvc5 and flags any
`MISMATCH` (a sound solver must produce **zero** sat↔unsat disagreements).

---

## Repository layout

| Path | Contents |
|---|---|
| `include/zolver/` | public API headers (`Solver.h`, …) |
| `src/expr/` | hash-consed Core IR, rewriter |
| `src/parser/` | SOMTParser adapter |
| `src/frontend/` | lowering passes, theory factory |
| `src/sat/` | CaDiCaL wrapper |
| `src/theory/core/` | TheoryManager, combination (Nelson–Oppen) |
| `src/theory/arith/` | `ArithSolverBase`, `Reasoner`, per-theory solvers |
| `src/theory/arith/nra/` | CDCAC engine, projection, Lazard tower |
| `src/theory/arith/nia/` | NIA-Core, bit-blast |
| `src/theory/arith/poly/` | libpoly polynomial kernel |
| `src/mcsat/`, `src/search/`, `src/omt/`, `src/proof/`, `src/learning/` | research paths (skeleton → in progress) |
| `tools/` | CLI, benchmark + deploy scripts, trace/proof/model checkers |
| `tests/` | doctest unit suite + per-logic regression corpora |
| `third_party/SOMTParser` | frontend parser (git submodule) |
| `reference/` | in-tree cvc5 / z3 copies — for *reading* only, not linked |
| `plan.md` | architectural master document (source of truth) |

---

## Project status

| Stage | Area | Status |
|---|---|---|
| A | Core IR, SAT, parser, lowering | ✅ functional |
| C / E | LRA, LIA | ✅ functional |
| D | NRA (CDCAC + presolve) | ✅ functional |
| I | NIA-Core (+ bit-blast) | ✅ functional |
| — | Arrays / combination (5 array logics) | ✅ functional |
| — | Lazard tower lift | 🧪 experimental (flag-gated) |
| F / G / H / J / K | MCSAT, advisor, OMT, proofs, learning | 🏗️ skeleton → in progress |

---

## License & provenance

Zolver is developed as autonomous-agent research. The `reference/` cvc5 and z3
copies are vendored for study only; the licensing posture relative to those
projects is unsettled, so no code is copied from them. See `plan.md` for the full
design rationale and `CLAUDE.md` for contributor (agent) guidance.
