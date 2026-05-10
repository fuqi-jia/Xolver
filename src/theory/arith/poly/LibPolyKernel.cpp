#include "theory/arith/poly/LibPolyKernel.h"

#ifdef NLCOLVER_HAS_LIBPOLY

#include <algorithm>
#include <functional>
#include <optional>
#include <set>
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
    revVarMap_[v.get_internal()] = key;
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
    std::vector<std::string> result;
    const auto& p = get(a);

    // Recursively collect all variables by traversing coefficients.
    std::set<lp_variable_t> found;
    std::function<void(const poly::Polynomial&)> collect = [&](const poly::Polynomial& poly) {
        if (poly::is_constant(poly)) return;
        lp_variable_t mv = poly::main_variable(poly).get_internal();
        if (found.insert(mv).second) {
            for (size_t i = 0; i <= poly::degree(poly); ++i) {
                collect(poly::coefficient(poly, i));
            }
        }
    };
    collect(p);

    for (lp_variable_t v : found) {
        auto it = revVarMap_.find(v);
        if (it != revVarMap_.end()) {
            result.push_back(it->second);
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

std::optional<mpz_class> LibPolyKernel::evalInteger(
    PolyId a,
    const std::unordered_map<std::string, mpz_class>& sample) const {

    poly::Assignment pa(ctx_);
    for (const auto& [name, val] : sample) {
        auto it = varMap_.find(name);
        if (it != varMap_.end()) {
            pa.set(it->second, poly::Value(poly::Integer(val)));
        }
    }
    poly::Value v = poly::evaluate(get(a), pa);
    if (poly::is_integer(v)) {
        const poly::Integer& i = poly::as_integer(v);
        return *poly::detail::cast_to_gmp(&i);
    }
    // Non-integer result (e.g. rational from division-like operation)
    // For integer evaluation, this shouldn't happen with integer inputs
    // on integer-coefficient polynomials, but handle gracefully.
    if (poly::is_rational(v)) {
        const poly::Rational& r = poly::as_rational(v);
        const mpq_class* q = poly::detail::cast_to_gmp(&r);
        if (q->get_den() == 1) {
            return q->get_num();
        }
    }
    return std::nullopt;
}

std::optional<int> LibPolyKernel::degree(PolyId a, std::string_view var) const {
    const auto& p = get(a);
    // If polynomial is constant, degree is 0
    if (poly::is_constant(p)) {
        return 0;
    }
    auto it = varMap_.find(std::string(var));
    if (it == varMap_.end()) {
        // Variable not in this kernel's context → not present in polynomial
        return 0;
    }
    poly::Variable pv = it->second;
    if (poly::main_variable(p) == pv) {
        return static_cast<int>(poly::degree(p));
    }
    // Variable is not the main variable. Check if it appears at all.
    // For now, we check by comparing the polynomial before/after substitution.
    // A simpler heuristic: if the polynomial has other variables, this var
    // may or may not appear. To be conservative:
    // TODO: proper term iteration for multi-var detection.
    // For NIA-Core Phase A, we rely on the fact that most univariate
    // polynomials will have their sole variable as main_variable.
    return std::nullopt;
}

std::optional<std::vector<mpz_class>> LibPolyKernel::getIntegerCoefficients(
    PolyId a, std::string_view var) const {

    const auto& p = get(a);
    if (poly::is_constant(p)) {
        // Constant polynomial: coefficient is the constant value
        mpq_class c = toConstant(a);
        if (c.get_den() != 1) return std::nullopt;
        return std::vector<mpz_class>{c.get_num()};
    }

    auto it = varMap_.find(std::string(var));
    if (it == varMap_.end()) return std::nullopt;
    poly::Variable pv = it->second;

    if (poly::main_variable(p) != pv) {
        // Variable is not main variable. Cannot extract coefficients via libpoly API.
        return std::nullopt;
    }

    std::size_t d = poly::degree(p);
    std::vector<mpz_class> coeffs;
    coeffs.reserve(d + 1);

    for (std::size_t k = 0; k <= d; ++k) {
        // coefficient(p, k) returns the coefficient of x^k as a polynomial
        // in the remaining variables. For a truly univariate polynomial,
        // each coefficient should be constant.
        poly::Polynomial coeff = poly::coefficient(p, k);
        if (!poly::is_constant(coeff)) {
            // Multi-variate or coefficient involves other variables
            return std::nullopt;
        }
        // Extract constant value directly without modifying pool
        poly::Assignment empty(ctx_);
        poly::Value v = poly::evaluate(coeff, empty);
        if (!poly::is_rational(v)) return std::nullopt;
        const poly::Rational& r = poly::as_rational(v);
        mpq_class c = *poly::detail::cast_to_gmp(&r);
        if (c.get_den() != 1) return std::nullopt;
        coeffs.push_back(c.get_num());
    }

    // coeffs currently from x^0 to x^d; reverse to x^d ... x^0 for RRT
    std::reverse(coeffs.begin(), coeffs.end());
    return coeffs;
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_LIBPOLY
