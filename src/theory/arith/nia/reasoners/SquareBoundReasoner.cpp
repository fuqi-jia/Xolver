#include "theory/arith/nia/reasoners/SquareBoundReasoner.h"
#include <cmath>

namespace nlcolver {

SquareBoundReasoner::SquareBoundReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

bool SquareBoundReasoner::extractSquareForm(PolyId poly,
                                            std::string& var,
                                            mpz_class& constant) const {
    auto vars = kernel_.variables(poly);
    if (vars.size() != 1) return false;
    var = vars[0];

    auto degOpt = kernel_.degree(poly, var);
    if (!degOpt || *degOpt != 2) return false;

    auto coeffsOpt = kernel_.getIntegerCoefficients(poly, var);
    if (!coeffsOpt) return false;
    const auto& coeffs = *coeffsOpt;
    if (coeffs.size() != 3) return false; // need [a, b, c] for ax^2 + bx + c

    // Must be x^2 + constant (no linear term, leading coeff == 1)
    if (coeffs[0] != 1 || coeffs[1] != 0) return false;

    constant = coeffs[2]; // constant term
    return true;
}

NiaReasoningResult SquareBoundReasoner::handleConstraint(
    const NormalizedNiaConstraint& c, DomainStore& domains) {

    std::string var;
    mpz_class constant;
    if (!extractSquareForm(c.poly, var, constant)) {
        return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }

    // poly = x^2 + constant,  constraint is (x^2 + constant) rel 0
    // i.e. x^2 rel (-constant)

    switch (c.rel) {
        case Relation::Leq: {
            // x^2 + constant <= 0  =>  x^2 <= -constant
            mpz_class negC = -constant;
            if (negC < 0) {
                // x^2 <= negative: impossible since x^2 >= 0
                return {NiaReasoningKind::Conflict,
                        TheoryConflict{{c.reason}},
                        std::nullopt};
            }
            // x^2 <= negC  =>  |x| <= floor(sqrt(negC))
            mpz_class bound;
            mpz_sqrt(bound.get_mpz_t(), negC.get_mpz_t());
            domains.addLowerBound(var, -bound, c.reason);
            domains.addUpperBound(var, bound, c.reason);
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }

        case Relation::Eq: {
            // x^2 + constant = 0  =>  x^2 = -constant
            mpz_class negC = -constant;
            if (negC < 0) {
                return {NiaReasoningKind::Conflict,
                        TheoryConflict{{c.reason}},
                        std::nullopt};
            }
            if (negC == 0) {
                domains.restrictToFiniteSet(var, {mpz_class(0)}, c.reason);
                return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
            }
            if (mpz_perfect_square_p(negC.get_mpz_t())) {
                mpz_class r;
                mpz_sqrt(r.get_mpz_t(), negC.get_mpz_t());
                domains.restrictToFiniteSet(var, {r, -r}, c.reason);
                return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
            }
            // -constant is positive but not a perfect square: no integer roots
            return {NiaReasoningKind::Conflict,
                    TheoryConflict{{c.reason}},
                    std::nullopt};
        }

        case Relation::Neq: {
            // x^2 + constant != 0  =>  x^2 != -constant
            mpz_class negC = -constant;
            if (negC == 0) {
                domains.excludeValue(var, mpz_class(0), c.reason);
                return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
            }
            if (mpz_perfect_square_p(negC.get_mpz_t())) {
                mpz_class r;
                mpz_sqrt(r.get_mpz_t(), negC.get_mpz_t());
                domains.excludeValue(var, r, c.reason);
                domains.excludeValue(var, -r, c.reason);
                return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
            }
            // x^2 != positive non-square: always true (tautology)
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
        }

        case Relation::Geq:
            // x^2 + constant >= 0  =>  x^2 >= -constant
            // This is a disjunction (|x| >= sqrt(-constant) or any x if -constant <= 0).
            // Defer to Phase 2.
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

        default:
            return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }
}

NiaReasoningResult SquareBoundReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains) {

    bool updated = false;

    for (const auto& c : constraints) {
        auto r = handleConstraint(c, domains);
        if (r.kind == NiaReasoningKind::Conflict) return r;
        if (r.kind == NiaReasoningKind::DomainUpdated) updated = true;
    }

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
