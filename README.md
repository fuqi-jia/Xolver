# Xolver

Xolver is an SMT solver for quantifier-free nonlinear arithmetic and its combinations with uninterpreted functions, arrays, and algebraic datatypes. A CaDiCaL-driven CDCL(T) core orchestrates theory solvers that reason over exact rational (GMP/MPFR) and real-algebraic (libpoly) arithmetic, with no floating point on the decision path. Incomplete reasoning yields `unknown` rather than an unsound verdict.

---

## Supported logics

| Family | Logics |
|---|---|
| Boolean / EUF | `QF_BOOL`, `QF_UF` |
| Linear real / integer | `QF_LRA`, `QF_LIA`, `QF_LIRA` |
| Difference logic | `QF_IDL`, `QF_RDL` |
| Nonlinear | `QF_NRA`, `QF_NIA`, `QF_NIRA` |
| UF + arithmetic | `QF_UFLRA`, `QF_UFLIA`, `QF_UFNRA`, `QF_UFNIA` |
| Arrays | `QF_AX`, `QF_ALIA`, `QF_ALRA`, `QF_AUFLIA`, `QF_AUFLRA`, `QF_ANIA`, `QF_AUFNIA` |
| Datatypes | `QF_DT`, `QF_UFDT`, `QF_UFDTNIA` |

---

## Architecture

```
                  SMT-LIB 2 input
                         │
                  SOMTParser           (frontend, git submodule)
                         │
                  Frontend lowering    (ToInt / div-mod / ITE)
                         │
   ┌──────────────────────────────────────────────────┐
   │ Core IR (Expr / Sort)        hash-consed DAG     │
   │ Polynomial view (PolyId)     libpoly kernel      │
   │ Evaluation view              local-search        │
   └─────────────────────┬────────────────────────────┘
                         │  Atomizer  (b_i ↔ theory atom_i)
                         ▼
                  CaDiCaL SAT engine   (CDCL(T) main loop)
                         │
                         ▼
   ┌──────────────────────────────────────────────────┐
   │ Theory solvers (ArithSolverBase + Reasoner)      │
   │   LRA / LIA      simplex + branch&bound          │
   │   IDL / RDL      Bellman-Ford difference         │
   │   NRA            CDCAC + Collins/Lazard          │
   │   NIA            NIA-Core + bit-blast            │
   │   NIRA / LIRA    mixed int/real                  │
   │   EUF / Arrays   e-graph + lazy axioms           │
   │   Datatypes      lazy constructor plugin         │
   └─────────────────────┬────────────────────────────┘
                         │  candidate models / conflicts
                         ▼
            ModelValidator    (gates every sat — exact)
            Advisor           (heuristic, propose-only)
```

---

## Building

Requires CMake ≥ 3.16, a C++17 compiler, GMP, and MPFR. CaDiCaL and libpoly are git submodules; nlohmann/json and doctest are fetched at configure time.

```bash
git clone --recursive git@github.com:fuqi-jia/Xolver.git
cd Xolver && mkdir build && cd build
cmake ..                 # Release (-O3) by default
cmake --build . -j2      # on WSL / low-RAM, keep -j bounded
```

CLI at `build/bin/xolver`. CMake options: `XOLVER_BUILD_TESTS`, `XOLVER_BUILD_TOOLS`, `XOLVER_ENABLE_PROOFS`, `XOLVER_STATIC_BUILD`.

---

## Usage

```bash
./build/bin/xolver solve input.smt2                  # sat / unsat / unknown
./build/bin/xolver solve --produce-models input.smt2 # with model
./build/bin/xolver model-check <model>               # validate a model
./build/bin/xolver proof-check <proof>               # check a proof certificate
```

---

## Testing

```bash
cd build && ctest                          # unit + per-logic regression
./build/tests/xolver_unit_tests            # unit only
python3 tools/run_regression.py --root tests/regression --solver build/bin/xolver
```

The regression harness compares each verdict against z3/cvc5 and flags any sat↔unsat disagreement.

---

## Repository layout

| Path | Contents |
|---|---|
| `src/expr/` | hash-consed Core IR, rewriter |
| `src/parser/`, `src/frontend/` | SOMTParser adapter, lowering passes |
| `src/sat/` | CaDiCaL wrapper |
| `src/theory/core/` | TheoryManager, Nelson–Oppen combination |
| `src/theory/arith/` | per-theory solvers (LRA/LIA/IDL/RDL/NRA/NIA/NIRA/LIRA) |
| `src/theory/{euf,array,datatype}/` | e-graph + lazy axioms |
| `tools/` | CLI, build/test/benchmark scripts |
| `tests/` | doctest unit suite + per-logic regression corpora |
| `third_party/SOMTParser`, `cadical`, `libpoly` | git submodules |

---

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). Third-party dependency manifest in [`NOTICE`](NOTICE).

Xolver does not call, wrap, link, or include source from any existing SMT solver. Comments citing cvc5, z3, or others are algorithmic attribution for published algorithms (CDCAC, Lazard projection, Nelson–Oppen); the implementations are independently written.

Xolver was developed with substantial assistance from AI coding agents (Claude Opus 4.7 / Sonnet 4.6, ChatGPT 5.5, Kimi 2.6), under the direction of the author.

### Citation

```bibtex
@software{xolver,
  title  = {Xolver: an SMT solver for nonlinear arithmetic},
  author = {Fuqi Jia and contributors},
  year   = {2026},
  url    = {https://github.com/fuqi-jia/Xolver}
}
```
