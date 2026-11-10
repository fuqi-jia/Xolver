#include "algebra/linear/LinearConstraintNormalizer.h"
#include <algorithm>
#include <cassert>
#include <stdexcept>

namespace xolver {

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

bool LinearConstraintNormalizer::canonicalizeSign(
    LinearFormKey& lhs, Relation& rel, mpq_class& rhs) {
    // Leading nonzero coefficient (terms are sorted by var name).
    bool negate = false;
    for (const auto& t : lhs.terms) {
        if (t.second != 0) { negate = (t.second < 0); break; }
    }
    if (!negate) return false;
    for (auto& t : lhs.terms) t.second = -t.second;
    rhs = -rhs;
    switch (rel) {
        case Relation::Leq: rel = Relation::Geq; break;
        case Relation::Geq: rel = Relation::Leq; break;
        case Relation::Lt:  rel = Relation::Gt;  break;
        case Relation::Gt:  rel = Relation::Lt;  break;
        case Relation::Eq:  case Relation::Neq:  break;  // symmetric under ×(-1)
    }
    return true;
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
            expr.terms.push_back({std::string(kernel.varName(term.powers[0].first)), mpq_class(term.coefficient)});
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
        normalizeIntegerConstraint(out.lhs, out.rel, out.rhs);
    }

    return out;
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

    // Linear-form constants are rational; an algebraic RHS (never from inputs)
    // cannot be a linear-form constant, so bail to "no effective constraint".
    auto rhsQ = payload.rhs.tryAsRational();
    if (!rhsQ) return std::nullopt;

    ZeroLinearConstraint z;
    z.rel = effRel;
    z.sort = sort;

    // payload encodes: lhs rel rhs
    // we want: (lhs - rhs) rel 0
    for (const auto& t : payload.lhs.terms) {
        z.expr.terms.push_back({t.first, t.second});
    }
    z.expr.constant = -*rhsQ;
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
// normalizeIntegerConstraint
// ============================================================================
void LinearConstraintNormalizer::normalizeIntegerConstraint(
    LinearFormKey& lhs, Relation& rel, mpq_class& rhs) {
    // A unit strictness adjustment is valid only when the whole form is
    // integer-valued. Scale both sides by a positive common denominator first.
    mpz_class scale = rhs.get_den();
    for (const auto& [name, coefficient] : lhs.terms)
        mpz_lcm(scale.get_mpz_t(), scale.get_mpz_t(), coefficient.get_den_mpz_t());
    if (scale != 1) {
        for (auto& [name, coefficient] : lhs.terms) coefficient *= scale;
        rhs *= scale;
    }
    if (rel == Relation::Lt) {
        rel = Relation::Leq;
        rhs -= 1;
    } else if (rel == Relation::Gt) {
        rel = Relation::Geq;
        rhs += 1;
    }
}

void LinearConstraintNormalizer::normalizePrimitiveConstraint(
    LinearFormKey& lhs, Relation& rel, mpq_class& rhs, SortKind sort) {
    if (sort != SortKind::Int && sort != SortKind::Real)
        throw std::invalid_argument("primitive linear normalization requires an arithmetic sort");

    LinearExpr expression;
    expression.terms.reserve(lhs.terms.size());
    for (const auto& [name, coefficient] : lhs.terms)
        expression.terms.push_back({name, coefficient});
    expression = canonicalize(std::move(expression));

    mpz_class denominator = 1;
    for (const auto& term : expression.terms)
        mpz_lcm(denominator.get_mpz_t(), denominator.get_mpz_t(), term.coeff.get_den_mpz_t());
    mpz_class divisor = 0;
    for (const auto& term : expression.terms) {
        const mpq_class integral = term.coeff * denominator;
        mpz_gcd(divisor.get_mpz_t(), divisor.get_mpz_t(), integral.get_num_mpz_t());
    }
    if (divisor == 0) divisor = 1;
    mpq_class scale(denominator, divisor);
    scale.canonicalize();
    lhs.terms.clear();
    lhs.terms.reserve(expression.terms.size());
    for (const auto& term : expression.terms)
        lhs.terms.push_back({term.var, mpq_class(term.coeff * scale)});
    rhs *= scale;
    canonicalizeSign(lhs, rel, rhs);

    if (sort == SortKind::Real || rel == Relation::Eq || rel == Relation::Neq) return;
    mpz_class floor, ceiling;
    mpz_fdiv_q(floor.get_mpz_t(), rhs.get_num_mpz_t(), rhs.get_den_mpz_t());
    mpz_cdiv_q(ceiling.get_mpz_t(), rhs.get_num_mpz_t(), rhs.get_den_mpz_t());
    switch (rel) {
        case Relation::Leq: rhs = floor; break;
        case Relation::Lt: rel = Relation::Leq; rhs = ceiling - 1; break;
        case Relation::Geq: rhs = ceiling; break;
        case Relation::Gt: rel = Relation::Geq; rhs = floor + 1; break;
        default: break;
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

} // namespace xolver
