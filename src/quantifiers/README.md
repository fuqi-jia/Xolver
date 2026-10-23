# Quantifier algorithms

This layer sits above `search` and `algebra` and below `applications`. Algorithms
consume SOMTParser native nodes and use domain-specific representations. Lower
layers cannot depend on this layer.

| Directory | Domain | Algorithm and output |
| --- | --- | --- |
| `integer` | Boolean and affine/divisibility integer formulas | Scoped elimination, free-variable models and optional traces |
| `boolean` | QBF | Reduced ordered BDDs with existential/universal abstraction |
| `bitvector` | Bool and fixed-width BitVec | Modular circuits, BDD abstraction and free-variable models |
| `real` | Bool and polynomial Real | Scoped prenex compilation, full CAD and exact algebraic models |

The finite-domain compiler is `FiniteFormula.cpp`; real syntax compilation is
`real/NativeFormula.cpp`. Integer compilation and elimination are exposed by
`integer/NativeFormula.h` and `integer/Elimination.h`. Algorithms preserve binder
identity, shadowing and arbitrary quantifier alternation. Free variables are
existential for satisfiability; models contain their values, not Skolem functions
for bound variables.

`analyzeFinite` also exposes projected model counting and lexicographic Boolean
or signed/unsigned bit-vector optimization. Projection existentially abstracts
the other free variables; an empty tuple has count zero or one. Counts use exact
integers, including unconstrained projected variables. These operations share
the compiler and Boolean diagrams with QBF/QBV solving; application-specific
problem and result contracts remain in `applications`.

Integer numeric congruence, CRT and witness calculations belong to
`algebra/integer`. Real polynomial operations and root isolation use the algebra
and search infrastructure. Fixed-width circuits use Boolean diagrams; the
integer bit-blaster's width-growing semantics are a different contract.

`Limits` supplies work, node, recursion, projection-polynomial and projection
matrix budgets to Boolean/BV/real algorithms. Integer algorithms have `pa::Limits`.
Zero disables the corresponding limit. The global solve deadline also applies.
These are resource limits, not switches selecting unimplemented algorithms.

Unsupported theory combinations or operators are reported explicitly. Quantified
UF, arrays, integer/real mixtures and integer/bit-vector conversions are outside
these signatures. An incomplete primitive computation cannot establish a
logical verdict. Integer traces have limited certificate coverage; Boolean/BV
and real quantifier solving do not emit independently replayable UNSAT proofs.
