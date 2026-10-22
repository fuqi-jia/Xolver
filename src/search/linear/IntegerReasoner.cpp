#include "search/linear/IntegerReasoner.h"
#include "algebra/linear/LinearConstraintNormalizer.h"
#include <algorithm>

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
    const std::vector<ActiveLinearAtom>& activeAtoms) {

    for (const auto& atom : activeAtoms) {
        auto nc = normalize(atom.lhs, atom.rhs, atom.rel, atom.value);
        if (!nc) continue;

        // 1. GCD equality conflict
        if (auto conflict = checkGcdEqualityConflict(*nc, atom.lit)) {
            return TheoryCheckResult::mkConflict(*conflict);
        }

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
