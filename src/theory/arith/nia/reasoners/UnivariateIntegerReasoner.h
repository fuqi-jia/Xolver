#pragma once

#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/core/TheorySolver.h"
#include <set>

namespace xolver {

enum class IntegerRootStatus { Complete, Incomplete };

struct IntegerRootResult {
    IntegerRootStatus status;
    std::set<mpz_class> roots;
    bool isZeroPolynomial = false;
};

/**
 * UnivariateIntegerReasoner: solves univariate integer polynomial constraints.
 *
 * - Integer equality roots via Rational Root Theorem
 * - Square bound inference (x^2 <= c → finite domain)
 * - Domain updates with reasons
 */
class UnivariateIntegerReasoner {
public:
    explicit UnivariateIntegerReasoner(PolynomialKernel& kernel);

    NiaReasoningResult run(const std::vector<NormalizedNiaConstraint>& constraints,
                           DomainStore& domains,
                           TheoryLemmaStorage& lemmaDb);

    // Complete divisor set of |n| (±), or complete=false if it cannot be
    // enumerated completely AND cheaply. Default: O(sqrt n) trial division +
    // infeasibility cap. XOLVER_NIA_DIVISOR_FACTOR: prime-factorization-based
    // enumeration (e.g. 2^256 -> {2:256} -> 257 divisors, fast) — closes the
    // O(sqrt n) RRT hang on large-but-factorable constants. Sound: complete=true
    // only when ALL divisors are enumerated (full factorization within the cap).
    // Public for direct unit testing of the soundness contract.
    static std::set<mpz_class> completeDivisors(const mpz_class& n, bool& complete);

private:
    PolynomialKernel& kernel_;

    // Find all integer roots of p(x) = 0 via RRT. Returns Complete if all divisors enumerated.
    IntegerRootResult findIntegerRoots(PolyId poly, const std::string& var, SatLit reason);

    // Test if a value is a root.
    bool isRoot(PolyId poly, const std::string& var, const mpz_class& val);

    // Enumerate all divisors of n (positive and negative).
    static std::set<mpz_class> divisors(const mpz_class& n);

    // Handle x^2 <= c type bounds.
    NiaReasoningResult handleSquareBound(const NormalizedNiaConstraint& c,
                                          DomainStore& domains);
};

} // namespace xolver
