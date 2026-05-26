#include "theory/arith/lia/GomoryCut.h"

namespace zolver {

mpq_class gmiFractionalPart(const mpq_class& q) {
    mpz_class fl;
    mpz_fdiv_q(fl.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
    mpq_class f = q - mpq_class(fl);
    // Defensive: keep in [0,1).
    if (f < 0) f += 1;
    if (f >= 1) f -= 1;
    return f;
}

std::optional<GomoryCutResult> deriveGomoryCut(const mpq_class& f0,
                                               const std::vector<GmiNonbasicTerm>& terms) {
    if (f0 <= 0 || f0 >= 1) return std::nullopt;  // basic var not fractional

    GomoryCutResult res;
    res.gamma.reserve(terms.size());
    res.rhs = mpq_class(1) - f0;   // cut: Σ frac(chat_j) y_j >= 1 - f0
    bool anyPositive = false;

    for (const auto& t : terms) {
        // The pure Gomory cut is sound only when y_j is a non-negative integer.
        // For any non-integer term, bail (emit no cut) rather than risk the
        // mixed-integer formula — soundness over coverage.
        if (!t.isInteger) return std::nullopt;
        mpq_class fj = gmiFractionalPart(t.coeff);  // gamma_j = frac(chat_j) >= 0
        if (fj > 0) anyPositive = true;
        res.gamma.push_back(std::move(fj));
    }

    // All coefficients integral -> cut is 0 >= 1-f0 (a constant infeasibility,
    // i.e. the row has no integer solution). The caller's other reasoning
    // (GCD/divisibility) owns that; we emit no cut here.
    if (!anyPositive) return std::nullopt;
    return res;
}

} // namespace zolver
