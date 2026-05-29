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
    // Trial-division bound: a residual with no factor <= B and <= B^2 is provably
    // prime. 1e7 (~10ms worst case) at the competition budget factors more
    // constants fully (vs the dev 1e6); 2^k constants never reach it anyway.
    static const mpz_class B("10000000");
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

std::set<mpz_class> UnivariateIntegerReasoner::completeDivisors(const mpz_class& n,
                                                               bool& complete) {
    // PRIME-FACTORIZATION is the SOLE path — it DISSOLVES the old O(sqrt n)
    // divisor cap (2^256 -> {2:256} -> 257 divisors in O(log n), where trial
    // division would do ~2^128 iterations). No env flag: factorization is always
    // strictly better (sound + fast), so it is the default, not a toggle.
    // complete=false (=> caller Incomplete => unknown, never the O(sqrt n) hang
    // and never UNSAT from a partial set) only when:
    //   (a) the constant has a large composite cofactor with no factor <= B and
    //       > B^2 (un-factorable cheaply — then |n| > B^2, so trial division
    //       would also be infeasible), or
    //   (b) the full divisor set would exceed MAX_DIVISORS (each divisor is one
    //       exact kernel root-test; 10000 is the competition-budget fallback cap).
    constexpr size_t MAX_DIVISORS = 10000;
    complete = true;
    bool fullyFactored = false;
    auto factors = primeFactorizeBounded(abs(n), fullyFactored);
    if (!fullyFactored) { complete = false; return {}; }
    bool ok = false;
    auto divs = divisorsFromFactors(factors, MAX_DIVISORS, ok);
    if (!ok) { complete = false; return {}; }
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
