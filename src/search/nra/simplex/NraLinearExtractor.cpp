#include "search/nra/simplex/NraLinearExtractor.h"
#include <algorithm>
#include <map>

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

std::vector<LinearAtom> linearizeMonomials(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& constraints) {
    using Monomial = std::vector<std::pair<VarId, int>>;
    std::map<Monomial, VarId> variables;
    std::vector<LinearAtom> result;
    for (const auto& constraint : constraints) {
        auto terms = kernel.terms(constraint.poly);
        if (!terms) continue;
        LinearAtom atom;
        atom.rel = constraint.rel;
        atom.reason = constraint.reason;
        std::map<VarId, mpq_class> coefficients;
        bool supported = true;
        for (const auto& term : *terms) {
            if (term.coefficient == 0) continue;
            if (term.powers.empty()) {
                atom.constant += mpq_class(term.coefficient);
                continue;
            }
            Monomial monomial(term.powers.begin(), term.powers.end());
            std::sort(monomial.begin(), monomial.end());
            // The kernel contract supplies positive exponents and unique
            // variables. Decline malformed terms rather than alias them.
            for (size_t i = 0; i < monomial.size(); ++i) {
                if (monomial[i].second <= 0 || monomial[i].first == NullVar ||
                    (i && monomial[i - 1].first == monomial[i].first))
                    supported = false;
            }
            if (!supported) break;
            if (variables.size() >= NullVar) return {};
            auto [it, inserted] = variables.emplace(
                std::move(monomial), static_cast<VarId>(variables.size()));
            (void)inserted;
            coefficients[it->second] += mpq_class(term.coefficient);
        }
        if (!supported) continue;
        for (auto& [variable, coefficient] : coefficients)
            if (coefficient != 0) atom.coeffs.emplace_back(variable, std::move(coefficient));
        result.push_back(std::move(atom));
    }
    return result;
}

} // namespace xolver
