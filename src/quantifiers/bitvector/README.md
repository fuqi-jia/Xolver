# Fixed-width bit-vector quantification

`Circuit` represents words as least-significant-bit-first Boolean diagrams.
Arithmetic wraps modulo the word width. Quantification abstracts all bits of
each binder; Boolean and bit-vector binders may alternate.

The native compiler supports bitwise operations, add/subtract/multiply,
signed and unsigned comparisons, division/remainder/modulo, shifts, concat,
extract, extensions, repeat, indexed rotations, `bvcomp`, negation overflow,
signed division overflow and signed/unsigned addition/multiplication overflow.
Division by zero and signed minimum divided by minus one follow SMT-LIB
fixed-width semantics. Integer conversions, arrays, UF and mixed arithmetic
require separate domain support and return `unknown` here.

Free-variable models use `(_ bvN width)` terms. Wide words are subject to the
same work and memory budgets as small words; there is no fixed maximum word
width imposed by the algorithm.

Semantics: [SMT-LIB FixedSizeBitVectors](https://smt-lib.org/theories-FixedSizeBitVectors.shtml)
and [derived bit-vector operators](https://smt-lib.org/logics-all.shtml).
