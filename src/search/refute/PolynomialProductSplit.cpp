#include "search/refute/PolynomialProductSplit.h"
#include "algebra/poly/CommonMonomialFactor.h"
#include "algebra/poly/RationalPolynomial.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "base/RuntimeConfig.h"
#include <fstream>

namespace xolver {

std::optional<TheoryLemma> splitZeroPolynomialProduct(
    PolyId polynomial, const std::vector<SatLit>& premises, PolynomialKernel& kernel,
    TheoryId theory, TheoryAtomRegistry& registry, TheoryLemmaStorage& lemmas) {
    if (premises.empty()) return std::nullopt;
    const auto terms = kernel.terms(polynomial);
    if (!terms) return std::nullopt;
    const auto factor = factorCommonMonomial(*terms);
    if (!factor) return std::nullopt;
    const bool constantQuotient = factor->quotient.size() == 1 &&
        factor->quotient.front().powers.empty();
    PolyId quotient = NullPoly;
    if (!constantQuotient) {
        RationalPolynomial polynomial;
        for (const auto& term : factor->quotient) {
            MonomialKey powers;
            for (const auto& [variable, exponent] : term.powers)
                powers.emplace_back(variable, static_cast<uint32_t>(exponent));
            polynomial.addTerm(powers, mpq_class(term.coefficient));
        }
        polynomial.normalize();
        polynomial *= mpq_class(1) / polynomial.terms().begin()->second;
        // Reuse the kernel's canonical conversion cache: rebuilding an
        // equivalent quotient must not create a fresh SAT atom on each check.
        quotient = polynomial.toPrimitiveInteger(kernel).poly;
    }
    if (!constantQuotient && quotient == NullPoly) return std::nullopt;

    TheoryLemma lemma;
    lemma.kind = LemmaKind::Entailment;
    for (const auto premise : premises) lemma.lits.push_back(premise.negated());
    for (const auto& [variable, exponent] : factor->powers) {
        (void)exponent;
        lemma.lits.push_back(registry.getOrCreatePolynomialAtom(
            kernel.mkVar(variable), Relation::Eq, 0, theory));
    }
    if (!constantQuotient)
        lemma.lits.push_back(registry.getOrCreatePolynomialAtom(quotient, Relation::Eq, 0, theory));
    if (!normalizeTheoryClause(lemma.lits) || lemmas.isInstalled(lemma)) return std::nullopt;
    lemmas.insertIfNew(lemma);
    const auto profile = config::read<config::ReadKind::ProfilePath>(
        "ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    if (!profile.empty()) {
        std::ofstream out(profile.string() + ".product-covers.log", std::ios::app);
        out << "theory=" << static_cast<unsigned>(theory)
            << " premises=" << premises.size() << " factors=" << factor->powers.size()
            << " quotient=" << !constantQuotient << " literals=" << lemma.lits.size() << '\n';
    }
    return lemma;
}

} // namespace xolver
