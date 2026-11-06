#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include "contracts/TheorySolver.h"
#include "search/refute/SignDefinitenessRefuter.h"
#include <span>

namespace xolver {

class TheoryAtomRegistry;

// From premises proving p=0 and an exact p=m*q decomposition, publish the
// complete cover: not(premise_1) or ... or factor_1=0 or ... or q=0. Valid over
// integers and reals; no candidate model or factorization oracle is used.
// Call only at Full effort, where newly registered atoms/clauses are delivered.
std::optional<TheoryLemma> splitZeroPolynomialProduct(
    PolyId polynomial, const std::vector<SatLit>& premises, PolynomialKernel& kernel,
    TheoryId theory, TheoryAtomRegistry& registry, TheoryLemmaStorage& lemmas);

// Partition an unresolved factor sign before incomplete numeric search. The
// clause x<0 or x=0 or x>0 is unconditional over both Int and Real; active
// bounds only select useful factors. Installed partitions are never repeated.
// Call at Full effort so registered atoms and the clause are delivered together.
std::optional<TheoryLemma> splitNonlinearVariableSigns(
    std::span<const SignRefuteConstraint> constraints, PolynomialKernel& kernel,
    TheoryId theory, TheoryAtomRegistry& registry, TheoryLemmaStorage& lemmas);

} // namespace xolver
