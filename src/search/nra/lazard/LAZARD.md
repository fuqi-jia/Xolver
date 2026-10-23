# Real-algebraic projection and lifting

This directory provides projection, algebraic-tower arithmetic, valuation and
root-isolation components for real search. Component completion flags record
whether their mathematical obligations were discharged. An incomplete result
cannot justify UNSAT.

## [H1] Algebraic-tower representation

`TowerContext` contains extension variables, monic defining polynomials and
real embeddings. `TowerKernel` reduces polynomial expressions modulo those
definitions. Exact inversion/division can fail on zero divisors or reducible
presentations. A quotient-ring zero test alone is not a complete test at an
arbitrarily selected real embedding.

## [H2] Root isolation and membership

`RationalRootIsolation` uses exact rational Sturm sequences. `TowerRootIsolation`
constructs rational norm candidates and checks their membership at the selected
embedding. `RootMembershipOracle` distinguishes membership, non-membership and
an inconclusive result. Unfiltered norm roots cannot be presented as exact roots
of the original tower polynomial.

## [H3] Valuation

`LazardValuationEngine` records derivative orders while specializing a
polynomial along the prefix. This supplies a nonzero residual when ordinary
specialization nullifies a polynomial. Unsupported tower operations make the
valuation incomplete.

## [H4] Projection

`LazardProjectionOperator` builds content, squarefree factors, leading/trailing
coefficients, discriminants and pairwise resultants. `LazardProjectionClosure`
organizes the resulting polynomials by variable level and records provenance.
`SubresultantChain` exposes exact principal subresultant coefficients with
matrix-dimension budgets.

`ProjectionClosure` supplies coefficient/PSC projection for ground search.
Quantified real solving has its own full iterated-reductum projection in
`quantifiers/real/Decomposition.cpp`; the two closure contracts are distinct.

## [H5] Section lifting

`LazardLifter` orders exact sections produced by tower isolation. Its interface
reports unsupported multi-polynomial merges explicitly. Callers must inspect
completion before constructing a certified covering.

## [H6] Resource and capability boundaries

Projection size, root isolation and tower operations can be incomplete.
`CdcacCore` combines projection and lifting status before accepting an UNSAT
cover. Component names do not imply complete evidence for an entire SMT query.

## [H7] Provenance and checking

Projection entries record operation, parent entries and eliminated variable.
Valuation and cell records carry local obligations. These records support
component-level checking; they do not certify parsing, preprocessing or the C++
implementation as a whole.
