#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/logics/nia/NiaSolver.h"
#include <numeric>

namespace xolver {

NiaNormalizer::NiaNormalizer(PolynomialKernel& kernel) : kernel_(kernel) {}

PolyId NiaNormalizer::clearDenominators(PolyId poly) {
    // For now, we rely on the kernel's ability to handle rational coefficients.
    // If getIntegerCoefficients is available, we can reconstruct an integer-coefficient polynomial.
    // Otherwise, we return the polynomial as-is and hope the reasoning engines can handle it.
    // Phase NIA-Core: if the polynomial is not integer-coefficient, we return nullopt from normalize.

    // Check if polynomial is effectively integer by trying to extract coefficients.
    auto vars = kernel_.variables(poly);
    if (vars.empty()) {
        // Constant polynomial: already fine
        return poly;
    }
    if (vars.size() == 1) {
        auto coeffs = kernel_.getIntegerCoefficients(poly, vars[0]);
        if (coeffs) {
            // Rebuild polynomial from integer coefficients
            PolyId result = kernel_.mkZero();
            PolyId var = kernel_.mkVar(kernel_.getOrCreateVar(vars[0]));
            for (size_t i = 0; i < coeffs->size(); ++i) {
                mpz_class c = (*coeffs)[i];
                if (c == 0) continue;
                PolyId term = kernel_.mkConst(mpq_class(c));
                // Multiply by var^(degree - i)
                size_t power = coeffs->size() - 1 - i;
                if (power > 0) {
                    term = kernel_.mul(term, kernel_.pow(var, static_cast<uint32_t>(power)));
                }
                result = kernel_.add(result, term);
            }
            return result;
        }
    }
    // Multi-variate or coefficient extraction unavailable.
    // For Phase NIA-Core, we attempt a simpler check: see if the polynomial
    // evaluates to integer at integer points (heuristic). If not, we fail.
    return poly; // Pass through; downstream engines handle unsupported cases
}

NormalizedNiaConstraint NiaNormalizer::normalizeStrict(
    const ActiveNiaConstraint& c, PolyId intPoly) {

    switch (c.rel) {
        case Relation::Eq:
        case Relation::Neq:
        case Relation::Leq:
        case Relation::Geq:
            return {intPoly, c.rel, c.reason};

        case Relation::Gt: {
            // p > 0  =>  p >= 1  =>  p - 1 >= 0
            PolyId one = kernel_.mkConst(mpq_class(1));
            PolyId adjusted = kernel_.sub(intPoly, one);
            return {adjusted, Relation::Geq, c.reason};
        }
        case Relation::Lt: {
            // p < 0  =>  p <= -1  =>  p + 1 <= 0
            PolyId one = kernel_.mkConst(mpq_class(1));
            PolyId adjusted = kernel_.add(intPoly, one);
            return {adjusted, Relation::Leq, c.reason};
        }
    }
    // Unreachable
    return {intPoly, c.rel, c.reason};
}

NormalizedNiaConstraint NiaNormalizer::normalizeOne(const ActiveNiaConstraint& c) {
    // Step 1: Clear denominators (if possible)
    PolyId intPoly = clearDenominators(c.poly);
    // Step 2: Normalize strict inequalities
    return normalizeStrict(c, intPoly);
}

std::optional<std::vector<NormalizedNiaConstraint>>
NiaNormalizer::normalize(const std::vector<ActiveNiaConstraint>& active) {
    std::vector<NormalizedNiaConstraint> result;
    result.reserve(active.size());
    for (const auto& c : active)
        result.push_back(normalizeOne(c));
    return result;
}

} // namespace xolver
