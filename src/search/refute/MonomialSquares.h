#pragma once

#include "algebra/poly/RationalPolynomial.h"
#include "base/WorkBudget.h"
#include <functional>
#include <optional>
#include <vector>

namespace xolver {

struct MonomialSquare {
    mpq_class coefficient;
    MonomialKey weight, left, right;
};

struct MonomialSquareDecomposition {
    RationalPolynomial remainder;
    std::vector<MonomialSquare> squares;
};

// Exact identity: polynomial = remainder + sum c*w*(left-right)^2.
// Only nonnegative coefficients and weights accepted by the caller are used.
// A partial decomposition is not a sign proof: the remainder must also be
// checked. Exhaustion propagates, and no integer-domain assumption is made.
MonomialSquareDecomposition decomposeMonomialSquares(
    const RationalPolynomial& polynomial,
    const std::function<bool(const MonomialKey&)>& nonnegative,
    WorkBudget& budget);

struct MonomialEquationReduction {
    RationalPolynomial quotient, remainder;
};

// When every leading coefficient is exactly divisible by the equation's
// leading monomial, compute p=q*equation+r with no rational functions.
// The caller chooses a pivot using its fixed variable order. This
// identity holds even where that monomial is zero; no nonzero premise is used.
std::optional<MonomialEquationReduction> reduceByMonomialEquation(
    const RationalPolynomial& polynomial, const RationalPolynomial& equation,
    VarId variable, WorkBudget& budget);

} // namespace xolver
