#include "search/nia/preprocess/NiaNormalizer.h"

namespace xolver {

NiaNormalizer::NiaNormalizer(PolynomialKernel& kernel) : kernel_(kernel) {}

NormalizedNiaConstraint NiaNormalizer::normalizeOne(const ActiveNiaConstraint& c) {
    switch (c.rel) {
        case Relation::Eq:
        case Relation::Neq:
        case Relation::Leq:
        case Relation::Geq:
            return {c.poly, c.rel, c.reason};
        case Relation::Gt:
            // An integer p is positive exactly when p - 1 >= 0.
            return {kernel_.sub(c.poly, kernel_.mkOne()), Relation::Geq, c.reason};
        case Relation::Lt:
            return {kernel_.add(c.poly, kernel_.mkOne()), Relation::Leq, c.reason};
    }
    return {c.poly, c.rel, c.reason};
}

std::vector<NormalizedNiaConstraint>
NiaNormalizer::normalize(const std::vector<ActiveNiaConstraint>& active) {
    std::vector<NormalizedNiaConstraint> result;
    result.reserve(active.size());
    for (const auto& constraint : active) result.push_back(normalizeOne(constraint));
    return result;
}

} // namespace xolver
