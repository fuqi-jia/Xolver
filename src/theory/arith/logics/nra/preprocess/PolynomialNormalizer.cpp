#include "theory/arith/logics/nra/preprocess/PolynomialNormalizer.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <sstream>

namespace xolver {

PolynomialNormalizer::PolynomialNormalizer(PolynomialKernel& kernel)
    : kernel_(kernel) {}

PolynomialNormalizer::CanonicalKey PolynomialNormalizer::canonicalKey(PolyId p) {
    auto rpOpt = RationalPolynomial::fromPolyId(p, kernel_);
    if (!rpOpt) {
        // Fallback: use kernel toString (non-canonical but deterministic within session)
        return kernel_.toString(p);
    }
    rpOpt->normalize();
    return canonicalKey(*rpOpt);
}

PolynomialNormalizer::CanonicalKey PolynomialNormalizer::canonicalKey(const RationalPolynomial& rp) {
    std::ostringstream oss;
    bool first = true;
    for (const auto& [key, coeff] : rp.terms()) {
        if (!first) oss << "+";
        first = false;
        oss << coeff.get_num() << "/" << coeff.get_den();
        for (const auto& [varId, exp] : key) {
            oss << ":" << varId << "^" << exp;
        }
    }
    if (first) {
        oss << "0";
    }
    return oss.str();
}

} // namespace xolver
