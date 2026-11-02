#include "search/linear/IntegerReasoner.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "algebra/linear/IntegerIntervalCombination.h"
#include "search/linear/LinearBoundPropagation.h"
#include <algorithm>
#include <unordered_map>

namespace xolver {

// ============================================================================
// Helpers
// ============================================================================

mpz_class IntegerReasoner::gcdAbs(const std::vector<std::pair<std::string, mpq_class>>& terms) {
    mpz_class g = 0;
    for (const auto& t : terms) {
        const mpq_class& c = t.second;
        if (c.get_den() != 1) {
            return mpz_class(1); // non-integer coefficient
        }
        mpz_class a = c.get_num();
        if (a < 0) a = -a;
        if (a == 0) continue;
        if (g == 0) {
            g = a;
        } else {
            mpz_class tmp;
            mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
            g = tmp;
        }
    }
    return g;
}

// ============================================================================
// Normalization
// ============================================================================

std::optional<NormalizedConstraint> IntegerReasoner::normalize(
    const LinearFormKey& lhs, const mpq_class& rhs,
    Relation rel, bool value) {

    // Step 1: If value=false, negate relation
    if (!value) {
        rel = negateRelation(rel);
    }

    // Scale rational coefficients and RHS together before integer rounding.
    // This is shared with the atom-registration normalizer so both boundaries
    // preserve the same integer witnesses.
    LinearFormKey effLhs = lhs;
    mpq_class effRhs = rhs;
    LinearConstraintNormalizer::normalizeIntegerConstraint(effLhs, rel, effRhs);
    if (rel == Relation::Geq) {
        rel = Relation::Leq;
        for (auto& t : effLhs.terms) t.second = -t.second;
        effRhs = -effRhs;
    }

    return NormalizedConstraint{effLhs, effRhs, rel};
}

// ============================================================================
// Run: all cheap integer reasoning
// ============================================================================

std::optional<TheoryCheckResult> IntegerReasoner::run(
    const std::vector<ActiveLinearAtom>& activeAtoms, TheoryEffort effort) {

    for (const auto& atom : activeAtoms) {
        auto nc = normalize(atom.lhs, atom.rhs, atom.rel, atom.value);
        if (!nc) continue;

        // 1. GCD equality conflict
        if (auto conflict = checkGcdEqualityConflict(*nc, atom.lit)) {
            return TheoryCheckResult::mkConflict(*conflict);
        }

        if (effort != TheoryEffort::Full) continue;
        if (auto lemma = checkGcdInequalityTightening(*nc, atom.lit)) {
            return TheoryCheckResult::mkLemma(*lemma);
        }
        if (auto lemma = singleVarBoundTighten(*nc, atom.lit)) {
            return TheoryCheckResult::mkLemma(*lemma);
        }
        if (auto lemma = normalizeEquality(*nc, atom.lit)) {
            return TheoryCheckResult::mkLemma(*lemma);
        }
    }

    return std::nullopt;
}

std::optional<TheoryConflict> IntegerReasoner::checkIntervalCombinationConflict(
    const std::vector<ActiveLinearAtom>& activeAtoms) {
    struct Band {
        std::optional<mpz_class> lower, upper;
        SatLit lowerReason{0, true}, upperReason{0, true};
    };
    std::unordered_map<LinearFormKey, Band, LinearFormKeyHash> bands;
    WorkBudget budget(8192);
    auto conflict = [](const Band& a, const Band& b) {
        std::vector<SatLit> reasons{a.lowerReason, a.upperReason, b.lowerReason, b.upperReason};
        std::sort(reasons.begin(), reasons.end(), [](SatLit x, SatLit y) {
            return x.var != y.var ? x.var < y.var : x.sign < y.sign;
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end(), [](SatLit x, SatLit y) {
            return x.var == y.var && x.sign == y.sign;
        }), reasons.end());
        return TheoryConflict{std::move(reasons)};
    };
    try {
        std::vector<LinearBoundRow> propagationRows;
        for (const auto& atom : activeAtoms) {
            budget.tick();
            auto nc = normalize(atom.lhs, atom.rhs, atom.rel, atom.value);
            if (!nc || (nc->rel != Relation::Eq && nc->rel != Relation::Leq)) continue;
            propagationRows.push_back({nc->lhs, nc->rel, nc->rhs, {atom.lit}});
            auto& form = nc->lhs;
            form.terms.erase(std::remove_if(form.terms.begin(), form.terms.end(),
                [](const auto& term) { return term.second == 0; }), form.terms.end());
            if (form.terms.size() < 2) continue;
            const auto divisor = gcdAbs(form.terms);
            if (divisor == 0) continue;
            for (auto& term : form.terms) term.second /= divisor;
            mpq_class bound = nc->rhs / divisor;
            const bool negative = form.terms.front().second < 0;
            if (negative) {
                for (auto& term : form.terms) term.second = -term.second;
                bound = -bound;
            }
            auto& band = bands[form];
            if (negative || nc->rel == Relation::Eq) {
                mpz_class lower;
                mpz_cdiv_q(lower.get_mpz_t(), bound.get_num_mpz_t(), bound.get_den_mpz_t());
                if (!band.lower || lower > *band.lower) {
                    band.lower = std::move(lower); band.lowerReason = atom.lit;
                }
            }
            if (!negative || nc->rel == Relation::Eq) {
                mpz_class upper;
                mpz_fdiv_q(upper.get_mpz_t(), bound.get_num_mpz_t(), bound.get_den_mpz_t());
                if (!band.upper || upper < *band.upper) {
                    band.upper = std::move(upper); band.upperReason = atom.lit;
                }
            }
            if (band.lower && band.upper && *band.lower > *band.upper)
                return conflict(band, band);
        }
        // Interval closure can refute several coupled forms before a branch
        // lemma is installed. It uses only this active context, so backtracking
        // needs no additional state and the simplex assignment is untouched.
        WorkBudget propagationBudget(262144);
        if (auto reasons = LinearBoundPropagation::findConflict(propagationRows,
                [](const std::string&) { return true; }, propagationBudget))
            return TheoryConflict{std::move(*reasons)};
        struct Bounded {
            const LinearFormKey* key;
            const Band* reasons;
            BoundedIntegerForm form;
            bool wide;
        };
        std::vector<Bounded> bounded;
        for (const auto& [key, band] : bands) {
            if (!band.lower || !band.upper) continue;
            BoundedIntegerForm form{{}, *band.lower, *band.upper};
            mpz_class norm = 0;
            for (const auto& term : key.terms) {
                form.coefficients.push_back(term.second.get_num());
                const mpz_class magnitude = abs(term.second.get_num());
                if (magnitude > norm) norm = magnitude;
            }
            const bool wide = form.upper - form.lower >= norm;
            bounded.push_back({&key, &band, std::move(form), wide});
        }
        // Stable ordering makes a resource-limited search independent of hash layout.
        std::sort(bounded.begin(), bounded.end(), [](const Bounded& a, const Bounded& b) {
            const auto& x = a.key->terms; const auto& y = b.key->terms;
            return std::lexicographical_compare(x.begin(), x.end(), y.begin(), y.end(),
                [](const auto& l, const auto& r) {
                    return l.first != r.first ? l.first < r.first : l.second < r.second;
                });
        });
        for (std::size_t i = 0; i < bounded.size(); ++i) {
            for (std::size_t j = i + 1; j < bounded.size(); ++j) {
                budget.tick();
                const auto& a = bounded[i]; const auto& b = bounded[j];
                // If each row's width exceeds every coefficient magnitude, any
                // combined interval is at least as wide as its possible gcd.
                if (a.wide && b.wide) continue;
                if (a.key->terms.size() != b.key->terms.size()) continue;
                bool sameCoordinates = true;
                for (std::size_t k = 0; k < a.key->terms.size(); ++k)
                    if (a.key->terms[k].first != b.key->terms[k].first) { sameCoordinates = false; break; }
                if (!sameCoordinates) continue;
                if (findIntegerIntervalConflict(a.form, b.form, budget))
                    return conflict(*a.reasons, *b.reasons);
            }
        }
    } catch (const ResourceExhausted&) {
        // A bounded cut search is optional; the main integer search continues.
    }
    return std::nullopt;
}

// ============================================================================
// GCD equality conflict
// ============================================================================

std::optional<TheoryConflict> IntegerReasoner::checkGcdEqualityConflict(
    const NormalizedConstraint& c, SatLit lit) {

    if (c.rel != Relation::Eq) return std::nullopt;

    mpz_class g = gcdAbs(c.lhs.terms);
    if (g == 0) {
        // No variables - constant equation
        if (c.rhs != 0) {
            return TheoryConflict{{lit}};
        }
        return std::nullopt;
    }

    mpz_class rhsInt = c.rhs.get_num();
    if (rhsInt % g != 0) {
        // g ∤ c => unsatisfiable
        return TheoryConflict{{lit}};
    }

    return std::nullopt;
}

// ============================================================================
// GCD inequality tightening
// ============================================================================

std::optional<TheoryLemma> IntegerReasoner::checkGcdInequalityTightening(
    const NormalizedConstraint& c, SatLit lit) {

    if (c.rel != Relation::Leq) return std::nullopt;
    if (!registry_) return std::nullopt;

    mpz_class g = gcdAbs(c.lhs.terms);
    if (g == 0 || g == 1) return std::nullopt;

    mpz_class rhsInt = c.rhs.get_num();
    mpz_class quotient;
    mpz_fdiv_q(quotient.get_mpz_t(), rhsInt.get_mpz_t(), g.get_mpz_t());
    mpz_class tightened = quotient * g;

    if (tightened >= rhsInt) return std::nullopt; // no tightening possible

    LinearFormKey tightenedLhs = c.lhs;
    mpq_class tightenedRhs = mpq_class(tightened, 1);

    auto tightenedLit = registry_->getOrCreateLinearBoundAtom(
        tightenedLhs, Relation::Leq, tightenedRhs, TheoryId::LIA);

    // No-op guard: if tightened atom is the same as original, skip
    if (tightenedLit.var == lit.var) return std::nullopt;

    // Lemma: original_lit => tightened_lit  (i.e. ~original_lit ∨ tightened_lit)
    return TheoryLemma{{lit.negated(), tightenedLit}};
}

// ============================================================================
// Single-variable bound tightening
// ============================================================================

std::optional<TheoryLemma> IntegerReasoner::singleVarBoundTighten(
    const NormalizedConstraint& c, SatLit lit) {

    if (c.rel != Relation::Leq && c.rel != Relation::Eq) return std::nullopt;
    if (c.lhs.terms.size() != 1) return std::nullopt;
    if (!registry_) return std::nullopt;

    const auto& [name, coeff] = c.lhs.terms[0];

    if (coeff.get_den() != 1) return std::nullopt;
    mpz_class a = coeff.get_num();
    mpz_class rhsInt = c.rhs.get_num();

    if (a == 0) return std::nullopt;

    LinearFormKey singleVarLhs;
    singleVarLhs.terms.push_back({name, mpq_class(1)});
    Relation tightenedRel;
    mpq_class tightenedRhs;

    if (a > 0) {
        // a·x <= c  =>  x <= floor(c / a)
        tightenedRel = Relation::Leq;
        mpz_class bound;
        mpz_fdiv_q(bound.get_mpz_t(), rhsInt.get_mpz_t(), a.get_mpz_t());
        tightenedRhs = mpq_class(bound, 1);
    } else {
        // a·x <= c with a < 0  =>  x >= ceil(c / a)
        // a < 0, so dividing by a flips sign.
        // Let a = -|a|. Then -|a|·x <= c  =>  |a|·x >= -c  =>  x >= ceil(-c / |a|)
        tightenedRel = Relation::Geq;
        mpz_class absA = -a;
        mpz_class negC = -rhsInt;
        mpz_class div;
        mpz_cdiv_q(div.get_mpz_t(), negC.get_mpz_t(), absA.get_mpz_t());
        tightenedRhs = mpq_class(div, 1);
    }

    auto tightenedLit = registry_->getOrCreateLinearBoundAtom(
        singleVarLhs, tightenedRel, tightenedRhs, TheoryId::LIA);

    // No-op guard: if tightened atom is the same as original, skip
    if (tightenedLit.var == lit.var) return std::nullopt;

    return TheoryLemma{{lit.negated(), tightenedLit}};
}

// ============================================================================
// Equality normalization
// ============================================================================

std::optional<TheoryLemma> IntegerReasoner::normalizeEquality(
    const NormalizedConstraint& c, SatLit lit) {

    if (c.rel != Relation::Eq) return std::nullopt;
    if (!registry_) return std::nullopt;

    mpz_class g = gcdAbs(c.lhs.terms);
    if (g == 0 || g == 1) return std::nullopt;

    mpz_class rhsInt = c.rhs.get_num();
    if (rhsInt % g != 0) {
        // Not divisible - should have been caught by GCD conflict
        return std::nullopt;
    }

    LinearFormKey normLhs = c.lhs;
    for (auto& t : normLhs.terms) {
        t.second /= mpq_class(g, 1);
    }
    mpq_class normRhs = c.rhs / mpq_class(g, 1);

    auto normLit = registry_->getOrCreateLinearBoundAtom(
        normLhs, Relation::Eq, normRhs, TheoryId::LIA);

    // No-op guard: if normalized atom is the same as original, skip
    if (normLit.var == lit.var) return std::nullopt;

    return TheoryLemma{{lit.negated(), normLit}};
}

} // namespace xolver
