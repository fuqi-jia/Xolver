#include "theory/arith/nra/simplex/NraLinearExtractor.h"

namespace xolver {

ClassifiedConstraints classifyConstraints(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints) {
    ClassifiedConstraints out;
    for (const auto& c : constraints) {
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) { out.nonlinear.push_back(c); continue; }  // conservative

        bool isLinear = true;
        for (const auto& t : *termsOpt) {
            int total = 0;
            for (const auto& pe : t.powers) total += pe.second;
            if (total >= 2) { isLinear = false; break; }
        }
        if (!isLinear) { out.nonlinear.push_back(c); continue; }

        LinearAtom la;
        la.rel = c.rel;
        la.reason = c.reason;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) la.constant += mpq_class(t.coefficient);
            else la.coeffs.push_back({ t.powers[0].first, mpq_class(t.coefficient) });
        }
        out.linear.push_back(std::move(la));
    }
    return out;
}

} // namespace xolver
