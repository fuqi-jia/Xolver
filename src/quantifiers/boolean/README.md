# Boolean quantification

`Diagram` implements reduced ordered binary decision diagrams with a unique
node table and memoized Boolean operations. Existential abstraction combines
the two cofactors with OR; universal abstraction uses AND. Arbitrary alternation
is evaluated from the native formula's innermost binders outward.

The native compiler supports Boolean connectives, equality, distinct, ite and
let, with fresh variables for each binder scope. A satisfying residual diagram
provides a model for free Boolean variables. No enumeration-width threshold is
imposed; work, node and recursion limits bound computation.

Algorithm reference: [Bryant, Graph-Based Algorithms for Boolean Function Manipulation](https://people.eecs.berkeley.edu/~russell/classes/cs289/f04/readings/Bryant%3A1986.pdf).
