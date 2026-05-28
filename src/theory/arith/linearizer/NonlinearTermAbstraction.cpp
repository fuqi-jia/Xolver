#include "theory/arith/linearizer/NonlinearTermAbstraction.h"
#include <algorithm>

namespace xolver {

NonlinearTermAbstraction::NonlinearTermAbstraction(PolynomialKernel& kernel)
    : kernel_(kernel) {}

std::optional<NonlinearTermKey> NonlinearTermAbstraction::detectNonlinearTerm(
    const PolynomialKernel::MonomialTerm& term) {

    const auto& powers = term.powers;

    // Product: x*y
    if (powers.size() == 2 &&
        powers[0].second == 1 && powers[1].second == 1) {
        NonlinearTermKey key;
        key.kind = NonlinearKind::Product;
        key.powers = powers;
        std::sort(key.powers.begin(), key.powers.end(),
                  [](auto& a, auto& b) { return a.first < b.first; });
        return key;
    }

    // Square: x^2
    if (powers.size() == 1 && powers[0].second == 2) {
        NonlinearTermKey key;
        key.kind = NonlinearKind::Square;
        key.powers = powers;
        return key;
    }

    // Linear or constant: not nonlinear
    if (powers.empty() ||
        (powers.size() == 1 && powers[0].second == 1)) {
        return std::nullopt;
    }

    // V1 unsupported (e.g., x^3, x*y*z, etc.)
    return std::nullopt;
}

AuxTerm NonlinearTermAbstraction::getOrCreateAux(const NonlinearTermKey& key) {
    auto it = auxCache_.find(key);
    if (it != auxCache_.end()) {
        return it->second;
    }

    std::string name = std::string(NL_AUX_PREFIX) + std::to_string(nextAuxId_++);
    VarId vid = kernel_.getOrCreateVar(name);
    PolyId poly = kernel_.mkVar(vid);

    AuxTerm aux{std::move(name), vid, poly, key};
    auxCache_.emplace(key, aux);
    return aux;
}

AbstractionResult NonlinearTermAbstraction::abstract(PolyId poly) {
    auto termsOpt = kernel_.terms(poly);
    if (!termsOpt) {
        return {poly, {}, true}; // unsupported
    }

    const auto& terms = *termsOpt;
    std::vector<AuxTerm> auxTerms;
    std::vector<PolynomialKernel::MonomialTerm> linearizedTerms;

    for (const auto& term : terms) {
        auto keyOpt = detectNonlinearTerm(term);
        if (!keyOpt) {
            // Linear or constant term: keep as-is
            linearizedTerms.push_back(term);
            continue;
        }

        // Nonlinear term: replace with aux * coeff
        AuxTerm aux = getOrCreateAux(*keyOpt);
        auxTerms.push_back(aux);

        PolynomialKernel::MonomialTerm newTerm;
        newTerm.coefficient = term.coefficient;
        newTerm.powers = {{aux.vid, 1}};
        linearizedTerms.push_back(std::move(newTerm));
    }

    // Build linearized polynomial from terms
    PolyId result = kernel_.mkConst(mpq_class(0));
    for (const auto& term : linearizedTerms) {
        PolyId termPoly = kernel_.mkConst(mpq_class(term.coefficient));
        for (const auto& [var, exp] : term.powers) {
            PolyId varPoly = kernel_.mkVar(var);
            if (exp == 1) {
                termPoly = kernel_.mul(termPoly, varPoly);
            } else {
                termPoly = kernel_.mul(termPoly, kernel_.pow(varPoly, static_cast<uint32_t>(exp)));
            }
        }
        result = kernel_.add(result, termPoly);
    }

    return {result, std::move(auxTerms), false};
}

} // namespace xolver
