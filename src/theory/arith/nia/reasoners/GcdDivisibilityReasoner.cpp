#include "theory/arith/nia/reasoners/GcdDivisibilityReasoner.h"

namespace xolver {

GcdDivisibilityReasoner::GcdDivisibilityReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult GcdDivisibilityReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints) {
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;  // inequalities carry slack

        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;

        mpz_class g = 0;          // gcd of non-constant monomial coefficients
        mpz_class constTerm = 0;  // the constant term coefficient c₀
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) {
                constTerm = t.coefficient;
            } else {
                mpz_class a = abs(t.coefficient);
                mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
            }
        }

        // g == 0: pure constant (left to trivial-constant stage).
        // g == 1: divides everything, no information.
        if (g <= 1) continue;

        // Σ aᵢ·mᵢ ≡ 0 (mod g) for integer mᵢ, so an integer solution of
        // Σ aᵢ·mᵢ + c₀ = 0 needs g | c₀; otherwise UNSAT.
        if (constTerm % g != 0) {
            return {NiaReasoningKind::Conflict,
                    TheoryConflict{{c.reason}},
                    std::nullopt};
        }
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
