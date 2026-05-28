#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include <cmath>
#include <cstdlib>

namespace xolver {

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

// Rational-root divisor enumeration trial-divides up to sqrt(|a0|). For huge
// constant terms (EVM mod-2^256 => |a0| ~ 2^256 => ~2^128 iterations) this is an
// effective hang. XOLVER_NIA_DIVISOR_CAP (default-OFF; promote after A/B) bails
// the root search to Incomplete when sqrt(|a0|) exceeds ~10^6 (|a0| > 10^12),
// turning a hang into a sound `unknown` (Incomplete is never read as UNSAT).
static bool divisorEnumerationInfeasible(const mpz_class& a0) {
    static const bool capEnabled = std::getenv("XOLVER_NIA_DIVISOR_CAP") != nullptr;
    if (!capEnabled) return false;
    static const mpz_class kThreshold("1000000000000");  // 10^12 = (10^6)^2
    return abs(a0) > kThreshold;
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
        if (divisorEnumerationInfeasible(a0_reduced)) {
            result.status = IntegerRootStatus::Incomplete;
            return result;
        }
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

    // RRT: all integer roots divide |a0|. But enumerating divisors trial-divides
    // up to sqrt(|a0|); for an EVM mod-2^256 constant term |a0| ~ 2^256 that is
    // ~2^128 bignum modulos — an effective hang. Bail to Incomplete BEFORE the
    // loop when sqrt(|a0|) exceeds a feasible trial bound (the existing
    // post-enumeration MAX_DIVISORS cap was too late — it computed the full set
    // first). Sound: Incomplete -> run() never derives UNSAT from empty roots.
    if (divisorEnumerationInfeasible(a0)) {
        result.status = IntegerRootStatus::Incomplete;
        return result;
    }
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
    TheoryLemmaStorage& /*lemmaDb*/) {

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
                        TheoryConflict{{c.reason}},
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
                            TheoryConflict{{c.reason}},
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
                            TheoryConflict{{c.reason}},
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

} // namespace xolver
