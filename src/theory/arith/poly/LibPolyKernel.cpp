#include "theory/arith/poly/LibPolyKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"

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

VarId LibPolyKernel::getOrCreateVar(std::string_view name) {
    std::string key(name);
    auto it = nameToVar_.find(key);
    if (it != nameToVar_.end()) return it->second;
    VarId id = static_cast<VarId>(varNames_.size());
    varNames_.push_back(key);
    poly::Variable v(ctx_, key.c_str());
    varIdToPolyVar_.push_back(v);
    polyVarToVarId_[v.get_internal()] = id;
    nameToVar_[std::move(key)] = id;
    return id;
}

std::optional<VarId> LibPolyKernel::findVar(std::string_view name) const {
    auto it = nameToVar_.find(std::string(name));
    if (it != nameToVar_.end()) return it->second;
    return std::nullopt;
}

std::string_view LibPolyKernel::varName(VarId v) const {
    if (v >= varNames_.size()) return "";
    return varNames_[v];
}

bool LibPolyKernel::isValidVar(VarId v) const {
    return v < varNames_.size();
}

poly::Variable LibPolyKernel::resolvePolyVar(VarId v) {
    if (v >= varIdToPolyVar_.size()) {
        // Should not happen if VarId was obtained through getOrCreateVar
        return poly::Variable(ctx_, "invalid");
    }
    return varIdToPolyVar_[v];
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
    // Non-integer rationals are not supported by libpoly's integer-ring polynomials.
    // Callers must clear denominators before constructing polynomials.
    // Returning NullPoly prevents silent unsoundness (e.g. 3/2 becoming 3).
    return NullPoly;
}

PolyId LibPolyKernel::mkVar(VarId v) {
    poly::Variable pv = resolvePolyVar(v);
    return alloc(poly::Polynomial(ctx_.get_polynomial_context(), pv));
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
        auto it = polyVarToVarId_.find(v);
        if (it != polyVarToVarId_.end()) {
            result.push_back(varNames_[it->second]);
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
        auto it = nameToVar_.find(name);
        if (it != nameToVar_.end()) {
            pa.set(varIdToPolyVar_[it->second], poly::Value(poly::Rational(val)));
        }
    }
    return poly::sgn(get(a), pa);
}

int LibPolyKernel::sgnVarId(PolyId a, const std::unordered_map<VarId, mpq_class>& sample) const {
    poly::Assignment pa(ctx_);
    for (const auto& [vid, val] : sample) {
        if (isValidVar(vid)) {
            pa.set(varIdToPolyVar_[vid], poly::Value(poly::Rational(val)));
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
        auto it = nameToVar_.find(name);
        if (it != nameToVar_.end()) {
            pa.set(varIdToPolyVar_[it->second], poly::Value(poly::Integer(val)));
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

std::optional<mpz_class> LibPolyKernel::evalIntegerVarId(
    PolyId a,
    const std::unordered_map<VarId, mpz_class>& sample) const {

    poly::Assignment pa(ctx_);
    for (const auto& [vid, val] : sample) {
        if (isValidVar(vid)) {
            pa.set(varIdToPolyVar_[vid], poly::Value(poly::Integer(val)));
        }
    }
    poly::Value v = poly::evaluate(get(a), pa);
    if (poly::is_integer(v)) {
        const poly::Integer& i = poly::as_integer(v);
        return *poly::detail::cast_to_gmp(&i);
    }
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
    auto it = nameToVar_.find(std::string(var));
    if (it == nameToVar_.end()) {
        // Variable not in this kernel's context → not present in polynomial
        return 0;
    }
    poly::Variable pv = varIdToPolyVar_[it->second];
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

    auto it = nameToVar_.find(std::string(var));
    if (it == nameToVar_.end()) return std::nullopt;
    poly::Variable pv = varIdToPolyVar_[it->second];

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

// Traverse data: holds result vector, kernel pointer, and failure flag
struct TermsTraverseData {
    std::vector<PolynomialKernel::MonomialTerm> terms;
    const LibPolyKernel* kernel;
    bool failed = false;
};

extern "C" {

// C callback for lp_polynomial_traverse
static void termsTraverseCallback(const lp_polynomial_context_t* /*ctx*/,
                                   lp_monomial_t* m, void* data) {
    auto* tdata = static_cast<TermsTraverseData*>(data);
    if (tdata->failed) return;

    // Extract coefficient: lp_integer_t -> poly::Integer -> mpz_class
    poly::Integer coeff(&m->a);
    mpz_class coeffMpz = *poly::detail::cast_to_gmp(&coeff);

    // Drop zero-coefficient terms
    if (coeffMpz == 0) return;

    PolynomialKernel::MonomialTerm term;
    term.coefficient = std::move(coeffMpz);

    for (size_t i = 0; i < m->n; ++i) {
        lp_variable_t v = m->p[i].x;
        size_t d = m->p[i].d;
        auto varOpt = tdata->kernel->resolveVariableId(v);
        if (!varOpt) {
            tdata->failed = true;
            return;
        }
        term.powers.push_back({*varOpt, static_cast<int>(d)});
    }

    tdata->terms.push_back(std::move(term));
}

} // extern "C"

std::optional<VarId> LibPolyKernel::resolveVariableId(lp_variable_t v) const {
    auto it = polyVarToVarId_.find(v);
    if (it != polyVarToVarId_.end()) return it->second;
    return std::nullopt;
}

poly::Variable LibPolyKernel::getVariable(const std::string& name) const {
    auto it = nameToVar_.find(name);
    if (it != nameToVar_.end()) return varIdToPolyVar_[it->second];
    // Variable not found: this should not happen if the polynomial was created
    // through this kernel. Return a dummy variable for safety.
    return poly::Variable(ctx_, name.c_str());
}

std::optional<std::vector<PolynomialKernel::MonomialTerm>>
LibPolyKernel::terms(PolyId a) const {
    const auto& p = get(a);

    // Constant polynomial: return single term with empty powers
    if (poly::is_constant(p)) {
        poly::Assignment empty(ctx_);
        poly::Value v = poly::evaluate(p, empty);
        if (!poly::is_rational(v)) return std::nullopt;
        const poly::Rational& r = poly::as_rational(v);
        mpq_class c = *poly::detail::cast_to_gmp(&r);
        if (c.get_den() != 1) return std::nullopt;
        return std::vector<MonomialTerm>{{c.get_num(), {}}};
    }

    TermsTraverseData data;
    data.kernel = this;
    lp_polynomial_traverse(p.get_internal(), termsTraverseCallback, &data);

    if (data.failed) return std::nullopt;
    return data.terms;
}

std::optional<PolyId> LibPolyKernel::pseudoRemainder(PolyId p, PolyId divisor) {
    const auto& pp = get(p);
    const auto& dd = get(divisor);
    try {
        poly::Polynomial r = poly::prem(pp, dd);
        return alloc(std::move(r));
    } catch (...) {
        return std::nullopt;
    }
}

std::optional<PolyId> LibPolyKernel::leadingCoefficient(PolyId p) {
    const auto& pp = get(p);
    if (poly::is_constant(pp)) return std::nullopt;
    try {
        poly::Polynomial lc = poly::leading_coefficient(pp);
        return alloc(std::move(lc));
    } catch (...) {
        return std::nullopt;
    }
}

std::optional<PolyId> LibPolyKernel::substituteRational(PolyId p, VarId v, const mpq_class& value) {
    auto termsOpt = terms(p);
    if (!termsOpt) return std::nullopt;

    // Build a RationalPolynomial from the substituted terms.
    // This avoids the mkConst non-integer restriction because we
    // normalize the whole substituted polynomial to integer coefficients
    // in one step via toPrimitiveInteger.
    RationalPolynomial rp;
    for (const auto& term : *termsOpt) {
        mpq_class coeff(term.coefficient);
        MonomialKey key;
        for (const auto& [varId, exp] : term.powers) {
            if (varId == v) {
                mpq_class factor(1);
                for (int i = 0; i < exp; ++i) factor *= value;
                coeff *= factor;
            } else {
                key.push_back({varId, exp});
            }
        }
        rp.addTerm(key, coeff);
    }
    rp.normalize();

    auto norm = rp.toPrimitiveInteger(*this);
    if (!norm.ok()) return std::nullopt;
    return norm.poly;
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_LIBPOLY
