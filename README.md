# NLColver

**N**on**L**inear **Co**nstraint So**lver**

A research-grade SMT/OMT solver platform with dual-engine architecture:
- **CDCL(T) / MCSAT** exact kernel for sound SAT/UNSAT reasoning
- **Local Search Advisor** for heuristic guidance and OMT optimization

## Status

🚧 **Early development** — Stage A (Reproducible SMT Core) in progress.

## Architecture Overview

```
SOMTParser (frontend)
       ↓
NLColver Core
├── Expr / Sort / Rewriter          (DAG-safe term layer)
├── Atomizer                         (theory atom extraction)
├── SAT Engine (CaDiCaL)             (CDCL boolean reasoning)
├── Theory Solvers
│   ├── LRA / LIA                    (rational simplex)
│   └── NRA (CAlC / CAC)             (exact CAD-like)
├── Polynomial Kernel (libpoly)      (algebraic numbers, root isolation)
├── Local Search Advisor             (heuristic suggestion only)
├── Proof / Certificate              (drat-lrat + cell certificates)
└── OMT Portfolio                    (exact + heuristic dual track)
```

## Build

Requirements:
- CMake ≥ 3.16
- C++17 compiler
- GMP / MPFR
- CaDiCaL (SAT backend)
- libpoly (polynomial kernel)

```bash
mkdir build && cd build
cmake ..
cmake --build .
ctest
```

## References

- [SOMTParser](https://github.com/fuqi-jia/SOMTParser) — SMT/OMT frontend parser
- [cvc5](https://github.com/cvc5/cvc5) — reference SMT solver
- [Z3](https://github.com/Z3Prover/z3) — reference SMT solver
