#include "search/refute/PolynomialProductSplit.h"
#include "algebra/poly/CommonMonomialFactor.h"
#include "algebra/poly/RationalPolynomial.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "base/RuntimeConfig.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <bit>
#include <fstream>
#include <map>

namespace xolver {

std::optional<TheoryLemma> splitNonlinearVariableSigns(
    std::span<const SignRefuteConstraint> constraints, PolynomialKernel& kernel,
    TheoryId theory, TheoryAtomRegistry& registry, TheoryLemmaStorage& lemmas) {
    constexpr unsigned negative = 1, zero = 2, positive = 4, any = 7;
    struct Candidate { VarId variable; size_t occurrences; unsigned signs; };
    try {
        WorkBudget work(0);
        std::map<VarId, size_t> factors;
        std::map<VarId, unsigned> signs;
        for (const auto& constraint : constraints) {
            work.tick();
            for (const auto& [word, coefficient] : constraint.poly.terms()) {
                (void)coefficient;
                // Odd powers expose an unresolved sign in a nonlinear term.
                // Even powers already have a known nonnegative sign.
                if (word.size() == 1 && word.front().second == 1) continue;
                for (const auto& [variable, exponent] : word) {
                    work.tick();
                    if (exponent % 2) ++factors[variable];
                }
            }
            std::optional<VarId> variable;
            mpq_class coefficient = 0, constant = 0;
            bool affine = true;
            for (const auto& [word, value] : constraint.poly.terms()) {
                work.tick();
                if (word.empty()) constant += value;
                else if (!variable && word.size() == 1 && word.front().second == 1) {
                    variable = word.front().first;
                    coefficient = value;
                } else { affine = false; break; }
            }
            if (!affine || !variable || coefficient == 0) continue;
            const mpq_class endpoint = -constant / coefficient;
            auto ordered = constraint.rel;
            if (coefficient < 0) {
                switch (constraint.rel) {
                    case Relation::Lt: ordered = Relation::Gt; break;
                    case Relation::Leq: ordered = Relation::Geq; break;
                    case Relation::Gt: ordered = Relation::Lt; break;
                    case Relation::Geq: ordered = Relation::Leq; break;
                    default: ordered = constraint.rel; break;
                }
            }
            unsigned allowed = any;
            switch (ordered) {
                case Relation::Eq: allowed = endpoint < 0 ? negative : endpoint > 0 ? positive : zero; break;
                case Relation::Neq: if (endpoint == 0) allowed = negative | positive; break;
                case Relation::Lt: if (endpoint <= 0) allowed = negative; break;
                case Relation::Leq: if (endpoint <= 0) allowed = endpoint < 0 ? negative : negative | zero; break;
                case Relation::Gt: if (endpoint >= 0) allowed = positive; break;
                case Relation::Geq: if (endpoint >= 0) allowed = endpoint > 0 ? positive : zero | positive; break;
            }
            const auto [entry, inserted] = signs.try_emplace(*variable, any);
            (void)inserted;
            entry->second &= allowed;
        }
        std::vector<Candidate> candidates;
        for (const auto& [variable, occurrences] : factors) {
            work.tick();
            const auto found = signs.find(variable);
            const unsigned possible = found == signs.end() ? any : found->second;
            if (std::popcount(possible) > 1) candidates.push_back({variable, occurrences, possible});
        }
        std::sort(candidates.begin(), candidates.end(), [](const auto& a, const auto& b) {
            const auto as = std::popcount(a.signs), bs = std::popcount(b.signs);
            if (as != bs) return as < bs;
            if (a.occurrences != b.occurrences) return a.occurrences > b.occurrences;
            return a.variable < b.variable;
        });
        size_t installed = 0;
        for (const auto& candidate : candidates) {
            work.tick();
            const auto polynomial = kernel.mkVar(candidate.variable);
            TheoryLemma lemma;
            lemma.kind = LemmaKind::Entailment;
            for (const auto relation : {Relation::Lt, Relation::Eq, Relation::Gt})
                lemma.lits.push_back(registry.getOrCreatePolynomialAtom(polynomial, relation, 0, theory));
            if (!normalizeTheoryClause(lemma.lits) || lemmas.isInstalled(lemma)) { ++installed; continue; }
            lemmas.insertIfNew(lemma);
            const auto profile = config::read<config::ReadKind::ProfilePath>(
                "ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
            if (!profile.empty()) {
                std::ofstream out(profile.string() + ".sign-partitions.log", std::ios::app);
                out << "theory=" << static_cast<unsigned>(theory)
                    << " factors=" << factors.size() << " unresolved=" << candidates.size()
                    << " installed=" << installed << " selected_signs=" << candidate.signs << '\n';
            }
            return lemma;
        }
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
    return std::nullopt;
}

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
