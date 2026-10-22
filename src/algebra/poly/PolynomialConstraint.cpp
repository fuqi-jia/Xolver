#include "algebra/poly/PolynomialConstraint.h"
#include <algorithm>

namespace xolver {

bool PolynomialConstraintKey::operator<(const PolynomialConstraintKey& other) const {
    if (relation != other.relation) return relation < other.relation;
    const auto& a = polynomial.terms();
    const auto& b = other.polynomial.terms();
    return std::lexicographical_compare(a.begin(), a.end(), b.begin(), b.end());
}

std::optional<CanonicalPolynomialConstraint>
canonicalPolynomialConstraint(RationalPolynomial polynomial, Relation relation) {
    polynomial.normalize();
    if (polynomial.isZero()) return std::nullopt;
    const mpq_class first = polynomial.terms().front().second;
    polynomial *= mpq_class(1) / first;
    if (first < 0) {
        switch (relation) {
            case Relation::Lt: relation = Relation::Gt; break;
            case Relation::Leq: relation = Relation::Geq; break;
            case Relation::Gt: relation = Relation::Lt; break;
            case Relation::Geq: relation = Relation::Leq; break;
            case Relation::Eq: case Relation::Neq: break;
        }
    }
    bool negated = false;
    switch (relation) {
        case Relation::Neq: relation = Relation::Eq; negated = true; break;
        case Relation::Gt: relation = Relation::Leq; negated = true; break;
        case Relation::Geq: relation = Relation::Lt; negated = true; break;
        case Relation::Eq: case Relation::Lt: case Relation::Leq: break;
    }
    return CanonicalPolynomialConstraint{{std::move(polynomial), relation}, negated};
}

} // namespace xolver
