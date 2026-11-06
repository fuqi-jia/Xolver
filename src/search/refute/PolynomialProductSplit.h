#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include "contracts/TheorySolver.h"

namespace xolver {

class TheoryAtomRegistry;

// From an asserted p=0 and an exact p=m*q decomposition, publish the complete
// cover: not(p=0) or factor_1=0 or ... or q=0. Valid over integers and reals;
// no bound, nonzero assumption, candidate model or factorization oracle is used.
// Call only at Full effort, where newly registered atoms/clauses are delivered.
std::optional<TheoryLemma> splitZeroPolynomialProduct(
    PolyId polynomial, SatLit premise, PolynomialKernel& kernel,
    TheoryId theory, TheoryAtomRegistry& registry, TheoryLemmaStorage& lemmas);

} // namespace xolver
