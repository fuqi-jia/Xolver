#include "theory/arith/nia/reasoners/UnivariateIntegerReasoner.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include <cmath>
#include <cstdlib>
#include <map>
#include <vector>

namespace xolver {

namespace {
// Prime-factorize |m| by trial-dividing primes up to a bound B. After the loop
// the residual has no factor <= B; if it also satisfies m <= B^2 it is
// DETERMINISTICALLY prime (any composite below B^2 must have a factor below B,
// which the loop would have found) — accept it. A residual above B^2 cannot be
// split cheaply and we DELIBERATELY do not trust a probabilistic primality test
// here: a false "prime" would under-enumerate divisors and could fabricate a
// false UNSAT, so we mark factorization INCOMPLETE (=> caller -> unknown). For
// 2^256 the `% 2` loop extracts {2:256} in 256 steps (residual 1, never hits the
// large-cofactor branch) — O(log n), not O(sqrt n).
std::map<mpz_class, int> primeFactorizeBounded(mpz_class m, bool& complete) {
    std::map<mpz_class, int> f;
    complete = true;
    if (m < 0) m = -m;
    if (m <= 1) return f;
    while (m % 2 == 0) { f[2]++; m /= 2; }
    static const mpz_class B("1000000");
    for (mpz_class d = 3; d <= B && d * d <= m; d += 2) {
        if (m % d == 0) { while (m % d == 0) { f[d]++; m /= d; } }
    }
    if (m > 1) {
        if (m <= B * B) f[m]++;       // no factor <= B and <= B^2 => provably prime
        else complete = false;        // large cofactor: cannot factor soundly+cheaply
    }
    return f;
}

// All divisors (±) from a prime factorization. ok=false if the divisor count
// (product of (exp+1)) would exceed maxCount (caller bails to Incomplete).
std::set<mpz_class> divisorsFromFactors(const std::map<mpz_class, int>& f,
                                        size_t maxCount, bool& ok) {
    ok = true;
    unsigned long long count = 1;
    for (const auto& kv : f) {
        count *= static_cast<unsigned long long>(kv.second + 1);
        if (count > maxCount) { ok = false; return {}; }
    }
    std::vector<mpz_class> pos = {mpz_class(1)};
    for (const auto& kv : f) {
        std::vector<mpz_class> next;
        next.reserve(pos.size() * (kv.second + 1));
        mpz_class pe = 1;
        for (int e = 0; e <= kv.second; ++e) {
            for (const auto& d : pos) next.push_back(d * pe);
            pe *= kv.first;
        }
        pos.swap(next);
    }
    std::set<mpz_class> result;
    for (const auto& d : pos) { result.insert(d); result.insert(-d); }
    return result;
}
} // namespace

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

std::set<mpz_class> UnivariateIntegerReasoner::completeDivisors(const mpz_class& n,
                                                               bool& complete) {
    // Read per call (not a one-time static) so unit tests can exercise both
    // modes in one process; this path runs once per univariate equation, not
    // in any inner loop, so the getenv cost is irrelevant.
    const bool factorMode = std::getenv("XOLVER_NIA_DIVISOR_FACTOR") != nullptr;
    constexpr size_t MAX_DIVISORS = 1000;
    complete = true;

    if (factorMode) {
        // Prime-factorization path: 2^256 -> {2:256} -> 257 divisors in O(log n),
        // vs O(sqrt n) = ~2^128 trial-division iterations. complete=false (=>
        // caller -> Incomplete -> unknown) when the constant cannot be fully
        // factored (large composite cofactor) or the divisor set exceeds the cap.
        bool fullyFactored = false;
        auto factors = primeFactorizeBounded(abs(n), fullyFactored);
        if (!fullyFactored) { complete = false; return {}; }
        bool ok = false;
        auto divs = divisorsFromFactors(factors, MAX_DIVISORS, ok);
        if (!ok) { complete = false; return {}; }
        return divs;
    }

    // Default path: O(sqrt n) trial division behind the infeasibility cap.
    if (divisorEnumerationInfeasible(n)) { complete = false; return {}; }
    auto divs = divisors(n);
    if (divs.size() > MAX_DIVISORS) { complete = false; return {}; }
    return divs;
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
        bool complete = true;
        auto divs = completeDivisors(a0_reduced, complete);
        if (!complete) {
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

    // RRT: all integer roots divide |a0|. completeDivisors enumerates the full
    // divisor set (factorization path for huge-but-factorable |a0| like 2^256,
    // else O(sqrt n) trial division behind the cap) or returns complete=false
    // when it cannot be enumerated soundly. Sound: Incomplete -> run() never
    // derives UNSAT from an empty/partial root set.
    bool complete = true;
    auto divs = completeDivisors(a0, complete);
    if (!complete) {
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
