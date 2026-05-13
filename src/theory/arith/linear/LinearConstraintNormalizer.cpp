#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include <algorithm>
#include <cassert>

namespace nlcolver {

// ============================================================================
// Canonicalize
// ============================================================================
LinearExpr LinearConstraintNormalizer::canonicalize(LinearExpr e) {
    std::sort(e.terms.begin(), e.terms.end(),
              [](const LinearTerm& a, const LinearTerm& b) {
                  return a.var < b.var;
              });

    std::vector<LinearTerm> merged;
    for (auto& t : e.terms) {
        if (t.coeff == 0) continue;
        if (!merged.empty() && merged.back().var == t.var) {
            merged.back().coeff += t.coeff;
            if (merged.back().coeff == 0) {
                merged.pop_back();
            }
        } else {
            merged.push_back(std::move(t));
        }
    }
    e.terms = std::move(merged);
    return e;
}

// ============================================================================
// fromPolynomialZero
// ============================================================================
std::optional<ZeroLinearConstraint> LinearConstraintNormalizer::fromPolynomialZero(
    const PolynomialKernel& kernel,
    PolyId poly,
    Relation rel,
    SortKind sort,
    const std::string& debugTag) {

    auto termsOpt = kernel.terms(poly);
    if (!termsOpt) return std::nullopt;

    LinearExpr expr;
    for (const auto& term : *termsOpt) {
        if (term.powers.empty()) {
            expr.constant += mpq_class(term.coefficient);
        } else if (term.powers.size() == 1 && term.powers[0].second == 1) {
            expr.terms.push_back({term.powers[0].first, mpq_class(term.coefficient)});
        } else {
            // Nonlinear term: degree > 1
            return std::nullopt;
        }
    }

    ZeroLinearConstraint z;
    z.expr = canonicalize(std::move(expr));
    z.rel = rel;
    z.sort = sort;
    z.debugTag = debugTag;
    return z;
}

// ============================================================================
// toLinearAtomSpec  (THE ONLY PLACE where constant is moved to rhs)
// ============================================================================
LinearAtomSpec LinearConstraintNormalizer::toLinearAtomSpec(const ZeroLinearConstraint& c) {
    LinearExpr e = canonicalize(c.expr);

    LinearAtomSpec out;
    out.rel = c.rel;
    out.sort = c.sort;
    out.debugTag = c.debugTag;

    // expr = constant + Σ a_i x_i
    // expr rel 0  <=>  Σ a_i x_i rel -constant
    for (const auto& t : e.terms) {
        out.lhs.terms.push_back({t.var, t.coeff});
    }
    out.rhs = -e.constant;

    if (out.sort == SortKind::Int) {
        normalizeStrictIntegerRelation(out.rel, out.rhs);
    }

    return out;
}

// ============================================================================
// registerLinearConstraint
// ============================================================================
SatLit LinearConstraintNormalizer::registerLinearConstraint(
    TheoryAtomRegistry& registry,
    const ZeroLinearConstraint& c,
    TheoryId targetTheory) {

    LinearAtomSpec spec = toLinearAtomSpec(c);
    return registry.getOrCreateLinearBoundAtom(spec.lhs, spec.rel, spec.rhs, targetTheory);
}

// ============================================================================
// makeEffectiveConstraint (LinearAtomPayload)
// ============================================================================
std::optional<ZeroLinearConstraint> LinearConstraintNormalizer::makeEffectiveConstraint(
    const LinearAtomPayload& payload,
    bool assignedValue,
    SortKind sort) {

    Relation effRel = assignedValue ? payload.rel : negateRelationForEffective(payload.rel);

    // V1: disequality is not a single linear bound
    if (effRel == Relation::Neq) {
        return std::nullopt;
    }

    ZeroLinearConstraint z;
    z.rel = effRel;
    z.sort = sort;

    // payload encodes: lhs rel rhs
    // we want: (lhs - rhs) rel 0
    for (const auto& t : payload.lhs.terms) {
        z.expr.terms.push_back({t.first, t.second});
    }
    z.expr.constant = -payload.rhs;
    z.expr = canonicalize(std::move(z.expr));

    return z;
}

// ============================================================================
// makeEffectiveConstraint (PolynomialAtomPayload)
// ============================================================================
std::optional<ZeroLinearConstraint> LinearConstraintNormalizer::makeEffectiveConstraint(
    const PolynomialAtomPayload& payload,
    bool assignedValue,
    SortKind sort,
    const PolynomialKernel& kernel) {

    Relation effRel = assignedValue ? payload.rel : negateRelationForEffective(payload.rel);

    if (effRel == Relation::Neq) {
        return std::nullopt;
    }

    auto opt = fromPolynomialZero(kernel, payload.poly, effRel, sort);
    return opt;
}

// ============================================================================
// normalizeStrictIntegerRelation
// ============================================================================
void LinearConstraintNormalizer::normalizeStrictIntegerRelation(Relation& rel, mpq_class& rhs) {
    if (rel == Relation::Lt) {
        rel = Relation::Leq;
        rhs -= 1;
    } else if (rel == Relation::Gt) {
        rel = Relation::Geq;
        rhs += 1;
    }
}

// ============================================================================
// negateRelationForEffective
// ============================================================================
Relation LinearConstraintNormalizer::negateRelationForEffective(Relation r) {
    switch (r) {
        case Relation::Eq:  return Relation::Neq;
        case Relation::Neq: return Relation::Eq;
        case Relation::Lt:  return Relation::Geq;
        case Relation::Leq: return Relation::Gt;
        case Relation::Gt:  return Relation::Leq;
        case Relation::Geq: return Relation::Lt;
    }
    return r; // unreachable
}

} // namespace nlcolver
