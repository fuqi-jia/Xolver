#include "theory/arith/nia/UnivariateIntegerReasoner.h"
#include "theory/arith/nia/IntegerModelValidator.h"
#include <cmath>

namespace nlcolver {

UnivariateIntegerReasoner::UnivariateIntegerReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::set<mpz_class> UnivariateIntegerReasoner::divisors(const mpz_class& n) {
    std::set<mpz_class> result;
    mpz_class abs_n = abs(n);
    if (abs_n == 0) return result;

    mpz_class limit = sqrt(abs_n);
    for (mpz_class d = 1; d <= limit; ++d) {
        if (abs_n % d == 0) {
            result.insert(d);
            result.insert(-d);
            mpz_class q = abs_n / d;
            if (q != d) {
                result.insert(q);
                result.insert(-q);
            }
        }
    }
    return result;
}

bool UnivariateIntegerReasoner::isRoot(PolyId poly,
                                       const std::string& var,
                                       const mpz_class& val) {
    IntegerModel model;
    model[var] = val;
    auto result = kernel_.evalInteger(poly, model);
    return result && *result == 0;
}

IntegerRootResult UnivariateIntegerReasoner::findIntegerRoots(
    PolyId poly, const std::string& var, SatLit /*reason*/) {

    IntegerRootResult result;
    result.status = IntegerRootStatus::Complete;

    if (kernel_.isZero(poly)) {
        result.isZeroPolynomial = true;
        return result;
    }

    auto coeffsOpt = kernel_.getIntegerCoefficients(poly, var);
    if (!coeffsOpt) {
        result.status = IntegerRootStatus::Incomplete;
        return result;
    }

    const auto& coeffs = *coeffsOpt;
    if (coeffs.empty()) {
        result.status = IntegerRootStatus::Incomplete;
        return result;
    }

    mpz_class a0 = coeffs.back();

    if (a0 == 0) {
        // Constant term is 0, so 0 is a root.
        result.roots.insert(0);

        // Factor out x^k where k is the number of trailing zero coefficients.
        // Find the effective polynomial after removing x factors.
        size_t effectiveSize = coeffs.size();
        while (effectiveSize > 1 && coeffs[effectiveSize - 1] == 0) {
            --effectiveSize;
        }
        if (effectiveSize <= 1) {
            return result; // P(x) = x^k, only root is 0
        }

        mpz_class a0_reduced = coeffs[effectiveSize - 1];
        auto divs = divisors(a0_reduced);

        constexpr size_t MAX_DIVISORS = 1000;
        if (divs.size() > MAX_DIVISORS) {
            result.status = IntegerRootStatus::Incomplete;
            return result;
        }

        for (const auto& d : divs) {
            if (d != 0 && isRoot(poly, var, d)) {
                result.roots.insert(d);
            }
        }
        return result;
    }

    // RRT: all integer roots divide |a0|
    auto divs = divisors(a0);

    constexpr size_t MAX_DIVISORS = 1000;
    if (divs.size() > MAX_DIVISORS) {
        result.status = IntegerRootStatus::Incomplete;
        return result;
    }

    for (const auto& d : divs) {
        if (isRoot(poly, var, d)) {
            result.roots.insert(d);
        }
    }

    return result;
}

NiaReasoningResult UnivariateIntegerReasoner::handleSquareBound(
    const NormalizedNiaConstraint& c, DomainStore& domains) {

    auto vars = kernel_.variables(c.poly);
    if (vars.size() != 1) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    auto degOpt = kernel_.degree(c.poly, vars[0]);
    if (!degOpt || *degOpt != 2) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult UnivariateIntegerReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    DomainStore& domains,
    TheoryLemmaDatabase& /*lemmaDb*/) {

    bool updated = false;

    for (const auto& c : constraints) {
        auto vars = kernel_.variables(c.poly);
        if (vars.size() != 1) continue;
        const std::string& var = vars[0];

        // Zero polynomial handling
        if (kernel_.isZero(c.poly)) {
            if (c.rel == Relation::Neq) {
                // 0 != 0 is UNSAT
                return {NiaReasoningKind::Conflict,
                        TheoryConflict{{c.reason.negated()}},
                        std::nullopt};
            }
            continue;
        }

        switch (c.rel) {
            case Relation::Eq: {
                auto rootResult = findIntegerRoots(c.poly, var, c.reason);
                if (rootResult.isZeroPolynomial) continue;
                if (rootResult.status == IntegerRootStatus::Complete && rootResult.roots.empty()) {
                    return {NiaReasoningKind::Conflict,
                            TheoryConflict{{c.reason.negated()}},
                            std::nullopt};
                }
                if (!rootResult.roots.empty()) {
                    domains.restrictToFiniteSet(var, rootResult.roots, c.reason);
                    updated = true;
                }
                break;
            }
            case Relation::Neq: {
                auto rootResult = findIntegerRoots(c.poly, var, c.reason);
                if (rootResult.isZeroPolynomial) {
                    return {NiaReasoningKind::Conflict,
                            TheoryConflict{{c.reason.negated()}},
                            std::nullopt};
                }
                if (rootResult.status == IntegerRootStatus::Complete && rootResult.roots.empty()) {
                    continue; // tautology
                }
                for (const auto& r : rootResult.roots) {
                    domains.excludeValue(var, r, c.reason);
                }
                if (!rootResult.roots.empty()) {
                    updated = true;
                }
                break;
            }
            case Relation::Leq:
            case Relation::Geq: {
                auto r = handleSquareBound(c, domains);
                if (r.kind == NiaReasoningKind::Conflict) return r;
                if (r.kind == NiaReasoningKind::DomainUpdated) updated = true;
                break;
            }
            case Relation::Lt:
            case Relation::Gt:
                break;
        }
    }

    if (updated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace nlcolver
