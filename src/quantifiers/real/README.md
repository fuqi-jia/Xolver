# Quantified polynomial real arithmetic

The compiler produces a prenex polynomial formula, freshening binders at every
occurrence. Boolean variables have domain `{0,1}`. Arithmetic supports rational
constants, addition, subtraction, multiplication, nonnegative numeral powers,
nonzero constant division, abs and ite. Unique-value witnesses encode arithmetic
ite/abs inside the enclosing binder scope.

`Decomposition` builds a full cylindrical algebraic decomposition in prefix
order. Projection includes coefficients and principal subresultant coefficients
for iterated reducta and their derivatives/pairs. Lifting visits real root
sections and the open sectors between them. Universal levels combine every
child with AND; existential levels combine them with OR. Sign-invariant partial
formulas permit short-circuiting. Free variables form the outer existential
block; models retain exact rational or isolated algebraic values.

Nullification is handled using the full coefficient projection. Algebraic root
isolation reports completion separately from an empty root set. Rational-prefix
isolation is cross-checked by an independent exact Sturm root count. Failed sign,
comparison or isolation operations cannot be interpreted as false formulas.
Work, polynomial count, projection matrix size, node and recursion budgets apply.

Variable division, transcendental functions, integer variables and uninterpreted
symbols are outside the polynomial real signature. The solver does not emit a
replayable CAD proof certificate.

Projection reference: [Davenport, Computer Algebra lectures](https://people.bath.ac.uk/masjhd/JHD-CA/JHD-CA20211215.pdf).
CAD background: [Brown, Quantifier Elimination by Cylindrical Algebraic Decomposition](https://www.usna.edu/Users/cs/wcbrown/research/qebycad/Tutorial/node6.html).

Existential coefficients followed by universal real polynomial identities use
coefficient matching when the resulting coefficient equations are linear. Exact
Gaussian elimination produces a rational model, which is checked by substitution
into every original polynomial. Other quantifier orders and nonlinear coefficient
systems retain the general decomposition path.
