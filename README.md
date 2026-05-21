# NLColver

**N**on**L**inear **Co**nstraint So**lver**

A research-grade SMT/OMT solver platform with dual-engine architecture:
- **CDCL(T) / MCSAT** exact kernel for sound SAT/UNSAT reasoning
- **Local Search Advisor** for heuristic guidance and OMT optimization

## Status

**Stages A–E functional, Stage I (NIA-Core) MVP complete.**

Core infrastructure (boolean, LRA, LIA, NRA) is operational. NIA-Core (Nonlinear Integer Arithmetic) now has a working pipeline covering univariate root finding, algebraic reasoning (square rules, GCD conflict, modular reasoning), bounded complete enumeration, and sound conflict generation.

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
│   ├── NRA (CAlC / CAC)             (exact CAD-like)
│   └── NIA (NIA-Core)               (univariate RRT + algebraic + bounded)
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

## Verified Logics (end-to-end)

| Logic | Example | Result |
|-------|---------|--------|
| QF_BOOL | `p ∧ q` | **sat** |
| QF_BOOL | `p ∧ ¬p` | **unsat** |
| QF_LRA | `x>0 ∧ x<10` | **sat** |
| QF_LRA | `x>0 ∧ x<0` | **unsat** |
| QF_LIA | `2x=1` (Int) | **unsat** |
| QF_LIA | `x≠0 ∧ x≥0 ∧ x≤0` | **unsat** |
| QF_NRA | `x²>2 ∧ x<0` | **sat** |
| QF_NRA | `x²>2 ∧ x²<1` | **unsat** |
| QF_NIA | `x²=4` | **sat** |
| QF_NIA | `x²=2` | **unsat** |
| QF_NIA | `0≤x≤10 ∧ x²=49` | **sat** |
| QF_NIA | `0≤x≤10 ∧ x²=50` | **unsat** |
| QF_NIA | `x²+y²=3` | **unsat** (modular) |
| QF_NIA | `0≤x≤3 ∧ 0≤y≤3 ∧ xy=6` | **sat** |

## References

- [SOMTParser](https://github.com/fuqi-jia/SOMTParser) — SMT/OMT frontend parser
- [cvc5](https://github.com/cvc5/cvc5) — reference SMT solver
- [Z3](https://github.com/Z3Prover/z3) — reference SMT solver


  ./tools/deploy_and_run.sh build

  # panda3: NIA 独占（25,452， unavoidable 大头）
  ./nlcolver-dist/tools/deploy_and_run.sh run nia -j 200 -t 100 --compare-with z3

  # panda4: 整数族（16,089）
  ./nlcolver-dist/tools/deploy_and_run.sh run lia,idl,rdl -j 200 -t 100 --compare-with z3

  # panda5: 实数族（13,907）
  ./nlcolver-dist/tools/deploy_and_run.sh run nra,lra -j 200 -t 100 --compare-with z3

  # panda6: UF 族 + 极小 logic（10,320）
  ./nlcolver-dist/tools/deploy_and_run.sh run uf,uflra,uflia,ufnia,ufnra,lira,nira -j 200 -t 100 --compare-with z3
