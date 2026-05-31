#include "theory/arith/lia/GomoryCut.h"

namespace xolver {

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

std::optional<GomoryCutResult> deriveGmiCut(const mpq_class& f0,
                                            const std::vector<GmiNonbasicTerm>& terms) {
    if (f0 <= 0 || f0 >= 1) return std::nullopt;  // basic var not fractional

    GomoryCutResult res;
    res.gamma.reserve(terms.size());
    res.rhs = f0;                        // cut: Σ psi_j y_j >= f0
    const mpq_class ratio = f0 / (mpq_class(1) - f0);   // f0/(1-f0) > 0
    bool anyPositive = false;

    for (const auto& t : terms) {
        // Standard-tableau coefficient ā_j = -chat_j (see header).
        mpq_class aj = -t.coeff;
        mpq_class psi;
        if (t.isInteger) {
            mpq_class fj = gmiFractionalPart(aj);        // frac(ā_j) ∈ [0,1)
            if (fj <= f0) {
                psi = fj;
            } else {
                psi = ratio * (mpq_class(1) - fj);
            }
        } else {
            // Continuous nonbasic: the branch the pure Gomory cut could not take.
            if (aj >= 0) {
                psi = aj;
            } else {
                psi = ratio * (-aj);
            }
        }
        // psi is always >= 0 by construction; clamp defensively against any
        // -0 representation so the downstream "gamma == 0 -> drop" test is exact.
        if (psi < 0) psi = 0;
        if (psi > 0) anyPositive = true;
        res.gamma.push_back(std::move(psi));
    }

    // Vacuous cut (every psi_j == 0): 0 >= f0 carries no information beyond the
    // row equation; let the caller branch / use other reasoning instead.
    if (!anyPositive) return std::nullopt;
    return res;
}

} // namespace xolver
