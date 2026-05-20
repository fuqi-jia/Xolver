#include "theory/arith/integer/IntegerReasoner.h"
#include <algorithm>

namespace nlcolver {

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

void IntegerReasoner::clearDenominators(LinearFormKey& lhs, mpq_class& rhs) {
    mpz_class lcm = 1;
    for (const auto& t : lhs.terms) {
        mpz_class den = t.second.get_den();
        if (den != 1) {
            mpz_class tmp;
            mpz_lcm(tmp.get_mpz_t(), lcm.get_mpz_t(), den.get_mpz_t());
            lcm = tmp;
        }
    }
    mpz_class rhsDen = rhs.get_den();
    if (rhsDen != 1) {
        mpz_class tmp;
        mpz_lcm(tmp.get_mpz_t(), lcm.get_mpz_t(), rhsDen.get_mpz_t());
        lcm = tmp;
    }

    if (lcm == 1) return;

    for (auto& t : lhs.terms) {
        t.second *= mpq_class(lcm, 1);
    }
    rhs *= mpq_class(lcm, 1);
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

    // Step 2: Convert strict to non-strict for LIA
    mpq_class effectiveRhs = rhs;
    switch (rel) {
        case Relation::Lt:
            // a·x < c  =>  a·x <= floor(c) if c is integer, else a·x <= floor(c)
            // For rationals: a·x < num/den  =>  a·x <= floor((num-1)/den)
            // More precisely: a·x < c  <=>  a·x <= c - epsilon
            // For integers: a·x <= floor(c - epsilon) = ceil(c) - 1 if c not integer
            // Actually for rationals: if c = p/q, strict < means <= (p-1)/q
            rel = Relation::Leq;
            effectiveRhs = mpq_class(rhs.get_num() - 1, rhs.get_den());
            break;
        case Relation::Gt:
            rel = Relation::Geq;
            effectiveRhs = mpq_class(rhs.get_num() + 1, rhs.get_den());
            break;
        case Relation::Eq:
        case Relation::Leq:
        case Relation::Geq:
        case Relation::Neq:
            break;
    }

    // Step 3: Convert >= to <= (multiply by -1)
    LinearFormKey effLhs = lhs;
    mpq_class effRhs = effectiveRhs;
    if (rel == Relation::Geq) {
        rel = Relation::Leq;
        for (auto& t : effLhs.terms) {
            t.second = -t.second;
        }
        effRhs = -effRhs;
    }

    // Step 4: Clear denominators
    clearDenominators(effLhs, effRhs);

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

        if (!safeMode_ && enableGcdIneqTightening_) {
            if (auto lemma = checkGcdInequalityTightening(*nc, atom.lit)) {
                return TheoryCheckResult::mkLemma(*lemma);
            }
        }
        if (!safeMode_ && enableSingleVarTightening_) {
            if (auto lemma = singleVarBoundTighten(*nc, atom.lit)) {
                return TheoryCheckResult::mkLemma(*lemma);
            }
        }
        if (!safeMode_ && enableEqGcdNormalization_) {
            if (auto lemma = normalizeEquality(*nc, atom.lit)) {
                return TheoryCheckResult::mkLemma(*lemma);
            }
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
    mpz_class tightened = (rhsInt / g) * g;

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
        tightenedRhs = mpq_class(rhsInt / a, 1);
    } else {
        // a·x <= c with a < 0  =>  x >= ceil(c / a)
        // a < 0, so dividing by a flips sign.
        // Let a = -|a|. Then -|a|·x <= c  =>  |a|·x >= -c  =>  x >= ceil(-c / |a|)
        tightenedRel = Relation::Geq;
        mpz_class absA = -a;
        mpz_class negC = -rhsInt;
        // ceil(negC / absA)
        mpz_class div = negC / absA;
        mpz_class rem = negC % absA;
        if (rem != 0) {
            // In C++ integer division truncates toward 0.
            // ceil(p/q) for integers: if p%q == 0, p/q; else (p/q) + 1 if q>0
            if ((negC > 0 && absA > 0) || (negC < 0 && absA < 0)) {
                div += 1;
            }
        }
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

} // namespace nlcolver
