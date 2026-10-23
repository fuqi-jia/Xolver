# Model counting

`Problem` contains native assertions and the explicit tuple of free variables
to count. Include unused declarations when their values belong to the counted
space. All other free symbols are existential. The empty tuple has one model
when the assertions are satisfiable, and zero otherwise.

The backend counts projected Boolean/BV valuations with BDD abstraction and
arbitrary-precision integer arithmetic. Quantified variables are not counted.
Results distinguish exact finite counts, infinity, invalid input and unknown;
unsupported domains return unknown, not a fabricated finite or infinite count.
