#include "theory/arith/poly/LibPolyKernel.h"

#ifdef NLCOLVER_HAS_LIBPOLY

#include <sstream>

namespace nlcolver {

LibPolyKernel::LibPolyKernel() = default;

PolyId LibPolyKernel::alloc(poly::Polynomial p) {
    PolyId id = static_cast<PolyId>(pool_.size());
    pool_.push_back(std::move(p));
    return id;
}

poly::Variable LibPolyKernel::resolveVar(std::string_view name) {
    std::string key(name);
    auto it = varMap_.find(key);
    if (it != varMap_.end()) return it->second;
    poly::Variable v(ctx_, key.c_str());
    varMap_[std::move(key)] = v;
    return v;
}

PolyId LibPolyKernel::mkZero() {
    return alloc(poly::Polynomial(ctx_.get_polynomial_context(), poly::Integer(0)));
}

PolyId LibPolyKernel::mkOne() {
    return alloc(poly::Polynomial(ctx_.get_polynomial_context(), poly::Integer(1)));
}

PolyId LibPolyKernel::mkConst(const mpq_class& c) {
    if (c.get_den() == 1) {
        return alloc(poly::Polynomial(ctx_.get_polynomial_context(), poly::Integer(c.get_num())));
    }
    // Non-integer rationals are not directly supported by libpoly's integer-ring
    // polynomials. Upper layers (Simplex, CAD) should clear denominators.
    // For now, return the numerator polynomial (approximate).
    // TODO: proper rational coefficient handling via scaling or Q-ring.
    return alloc(poly::Polynomial(ctx_.get_polynomial_context(), poly::Integer(c.get_num())));
}

PolyId LibPolyKernel::mkVar(std::string_view name) {
    poly::Variable v = resolveVar(name);
    return alloc(poly::Polynomial(ctx_.get_polynomial_context(), v));
}

PolyId LibPolyKernel::add(PolyId a, PolyId b) {
    return alloc(poly::operator+(get(a), get(b)));
}

PolyId LibPolyKernel::sub(PolyId a, PolyId b) {
    return alloc(poly::operator-(get(a), get(b)));
}

PolyId LibPolyKernel::neg(PolyId a) {
    return alloc(poly::operator-(get(a)));
}

PolyId LibPolyKernel::mul(PolyId a, PolyId b) {
    return alloc(poly::operator*(get(a), get(b)));
}

PolyId LibPolyKernel::pow(PolyId a, uint32_t k) {
    return alloc(poly::pow(get(a), k));
}

bool LibPolyKernel::isZero(PolyId a) const {
    return poly::is_zero(get(a));
}

bool LibPolyKernel::isConstant(PolyId a) const {
    return poly::is_constant(get(a));
}

mpq_class LibPolyKernel::toConstant(PolyId a) const {
    // libpoly constant polynomial: extract by evaluating at empty assignment
    poly::Assignment empty(ctx_);
    poly::Value v = poly::evaluate(get(a), empty);
    // v should be a rational value
    if (poly::is_rational(v)) {
        const poly::Rational& r = poly::as_rational(v);
        return *poly::detail::cast_to_gmp(&r);
    }
    return mpq_class(0);
}

std::vector<std::string> LibPolyKernel::variables(PolyId a) const {
    // Iterate over variable map and check which ones appear in the polynomial.
    // This is O(n_vars) which is fine for small polynomials.
    std::vector<std::string> result;
    const auto& p = get(a);
    for (const auto& [name, var] : varMap_) {
        // libpoly doesn't expose a direct "contains(var)" API on the C++ wrapper,
        // but we can check if the polynomial's main variable or coefficients
        // mention this variable. For a robust check we'd need to iterate terms.
        // Simplified: check if main_variable == var (only catches top variable).
        // TODO: proper term iteration when needed.
        if (poly::main_variable(p) == var) {
            result.push_back(name);
        }
    }
    return result;
}

bool LibPolyKernel::eq(PolyId a, PolyId b) const {
    return poly::operator==(get(a), get(b));
}

int LibPolyKernel::sgn(PolyId a, const std::unordered_map<std::string, mpq_class>& sample) const {
    poly::Assignment pa(ctx_);
    for (const auto& [name, val] : sample) {
        auto it = varMap_.find(name);
        if (it != varMap_.end()) {
            pa.set(it->second, poly::Value(poly::Rational(val)));
        }
    }
    return poly::sgn(get(a), pa);
}

std::string LibPolyKernel::toString(PolyId a) const {
    std::ostringstream oss;
    oss << get(a);
    return oss.str();
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_LIBPOLY
