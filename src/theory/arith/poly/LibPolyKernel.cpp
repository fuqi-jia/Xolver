#include "theory/arith/poly/LibPolyKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"

#ifdef XOLVER_HAS_LIBPOLY

// NB: the libpoly C declarations we use below (lp_variable_order_*,
// lp_variable_list_*, lp_polynomial_ensure_order / _new_copy) are pulled in
// transitively by polyxx.h (via LibPolyKernel.h). Do NOT add <poly/...>
// includes here — that resolves to the system headers and clashes with the
// vendored third_party/libpoly headers (duplicate typedefs / enums).

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <optional>
#include <set>
#include <sstream>
#include <unordered_map>     // S2 — tpiCache_ map

namespace xolver {

// S2 (P6) — hash + equality for RationalPolynomial cache keys. Hash mixes
// monomial-key (varId, exp) pairs with the leading mpz limbs of each rational
// coefficient — sufficient for unordered_map bucket dispersion. Equality is
// exact via FlatMonomialMap's operator==. O(N) per hash where N = #terms.
namespace {
struct RPHash {
    size_t operator()(const RationalPolynomial& rp) const noexcept {
        size_t h = 1469598103934665603ULL;             // FNV-1a 64 offset
        const size_t fnvP = 1099511628211ULL;
        for (const auto& [key, coeff] : rp.terms()) {
            for (const auto& [v, e] : key) {
                h ^= (static_cast<uint64_t>(v) << 16) | static_cast<uint64_t>(e);
                h *= fnvP;
            }
            const mpz_srcptr num = coeff.get_num().get_mpz_t();
            const mpz_srcptr den = coeff.get_den().get_mpz_t();
            const int ns = num->_mp_size, ds = den->_mp_size;
            const uint64_t nl0 = (ns != 0) ? mpz_getlimbn(num, 0) : 0ULL;
            const uint64_t dl0 = (ds != 0) ? mpz_getlimbn(den, 0) : 0ULL;
            h ^= static_cast<uint64_t>(ns) * 31ULL + nl0; h *= fnvP;
            h ^= static_cast<uint64_t>(ds) * 31ULL + dl0; h *= fnvP;
        }
        return h;
    }
};
struct RPEq {
    bool operator()(const RationalPolynomial& a, const RationalPolynomial& b) const noexcept {
        return a.terms() == b.terms();
    }
};
} // anonymous

struct LibPolyKernel::TpiCacheImpl {
    std::unordered_map<RationalPolynomial, std::pair<PolyId, mpq_class>, RPHash, RPEq> map;
};

std::optional<std::pair<PolyId, mpq_class>>
LibPolyKernel::tpiCacheLookup(const RationalPolynomial& rp) const {
    if (!tpiCache_) { ++tpiMisses_; return std::nullopt; }
    auto it = tpiCache_->map.find(rp);
    if (it == tpiCache_->map.end()) { ++tpiMisses_; return std::nullopt; }
    ++tpiHits_;
    return it->second;
}

void LibPolyKernel::tpiCacheStore(const RationalPolynomial& rp, PolyId p, const mpq_class& scale) {
    if (!tpiCache_) tpiCache_ = std::make_unique<TpiCacheImpl>();
    tpiCache_->map.emplace(rp, std::pair<PolyId, mpq_class>{p, scale});
}

LibPolyKernel::LibPolyKernel() = default;

LibPolyKernel::~LibPolyKernel() {
    // S1 + S1b + S2 + S1c (P6 / Task J) — env-gated stats dump for hit-rate sanity. Default no-op.
    if (std::getenv("XOLVER_NRA_KERNEL_STATS") != nullptr) {
        const uint64_t total = binOpHits_ + binOpMisses_;
        const double hitRate = total ? 100.0 * static_cast<double>(binOpHits_) / static_cast<double>(total) : 0.0;
        const uint64_t tpiTotal = tpiHits_ + tpiMisses_;
        const double tpiRate = tpiTotal ? 100.0 * static_cast<double>(tpiHits_) / static_cast<double>(tpiTotal) : 0.0;
        const size_t tpiSize = tpiCache_ ? tpiCache_->map.size() : 0;
        const uint64_t termsTotal = termsHits_ + termsMisses_;
        const double termsRate = termsTotal ? 100.0 * static_cast<double>(termsHits_) / static_cast<double>(termsTotal) : 0.0;
        std::fprintf(stderr,
            "[XOLVER_NRA_KERNEL_STATS] binOp hits=%llu misses=%llu hit_rate=%.2f%% cache=%zu | tpi hits=%llu misses=%llu hit_rate=%.2f%% cache=%zu | terms hits=%llu misses=%llu hit_rate=%.2f%% cache=%zu | sqfFactorsCache=%zu pool=%zu\n",
            (unsigned long long)binOpHits_, (unsigned long long)binOpMisses_, hitRate, binOpCache_.size(),
            (unsigned long long)tpiHits_,   (unsigned long long)tpiMisses_,  tpiRate, tpiSize,
            (unsigned long long)termsHits_, (unsigned long long)termsMisses_, termsRate, termsCache_.size(),
            sqfFactorsCache_.size(), pool_.size());
    }
}

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
    auto it = varToPoly_.find(v);
    if (it != varToPoly_.end()) {
        return it->second;
    }
    poly::Variable pv = resolvePolyVar(v);
    PolyId id = alloc(poly::Polynomial(ctx_.get_polynomial_context(), pv));
    varToPoly_[v] = id;
    return id;
}

// S1 (P6 cas/sqrtmodinv cac-deep): hash-cons every binary op. The wipeout
// cluster's hot path is RationalPolynomial::toPrimitiveInteger's divide-and-
// conquer build (RationalPolynomial.cpp:334-357) firing repeatedly for the
// SAME RP (SingleCellProjection step 0+1 double round-trip + factor reconv).
// libpoly polynomials are immutable post-alloc, so caching (op, operand-ids)
// is sound — a NullPoly arg short-circuits the cache (low-30-bit truncation
// would collide with a legitimate slot and silently return the wrong result;
// the un-cached path matches the pre-S1 crash semantics for that bug class).
PolyId LibPolyKernel::add(PolyId a, PolyId b) {
    if (a == NullPoly || b == NullPoly) return alloc(poly::operator+(get(a), get(b)));
    const PolyId lo = a < b ? a : b, hi = a < b ? b : a;   // commutative canonical
    const uint64_t key = binOpKey(0, lo, hi);
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    PolyId r = alloc(poly::operator+(get(a), get(b)));
    binOpCache_.emplace(key, r);
    return r;
}

PolyId LibPolyKernel::sub(PolyId a, PolyId b) {
    if (a == NullPoly || b == NullPoly) return alloc(poly::operator-(get(a), get(b)));
    const uint64_t key = binOpKey(1, a, b);                 // NOT commutative
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    PolyId r = alloc(poly::operator-(get(a), get(b)));
    binOpCache_.emplace(key, r);
    return r;
}

PolyId LibPolyKernel::neg(PolyId a) {
    if (a == NullPoly) return alloc(poly::operator-(get(a)));
    const uint64_t key = binOpKey(2, a, 0);                 // unary — slot b = 0
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    PolyId r = alloc(poly::operator-(get(a)));
    binOpCache_.emplace(key, r);
    return r;
}

PolyId LibPolyKernel::mul(PolyId a, PolyId b) {
    if (a == NullPoly || b == NullPoly) return alloc(poly::operator*(get(a), get(b)));
    const PolyId lo = a < b ? a : b, hi = a < b ? b : a;   // commutative canonical
    const uint64_t key = binOpKey(3, lo, hi);
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    PolyId r = alloc(poly::operator*(get(a), get(b)));
    binOpCache_.emplace(key, r);
    return r;
}

PolyId LibPolyKernel::pow(PolyId a, uint32_t k) {
    if (a == NullPoly) return alloc(poly::pow(get(a), k));
    const uint64_t key = binOpKey(4, a, k);                 // slot b carries k
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    PolyId r = alloc(poly::pow(get(a), k));
    binOpCache_.emplace(key, r);
    return r;
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
    // Variable is not the main variable: iterate terms to find max exponent.
    int maxDeg = 0;
    bool found = false;
    auto termsOpt = terms(a);
    if (termsOpt) {
        for (const auto& term : *termsOpt) {
            for (const auto& [vid, exp] : term.powers) {
                if (vid == it->second) {
                    maxDeg = std::max(maxDeg, exp);
                    found = true;
                    break;
                }
            }
        }
    }
    if (found) {
        return maxDeg;
    }
    // Variable does not appear in any term.
    return 0;
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
    // S1c (Task J): hash-cons. PolyId is immutable for the kernel's
    // lifetime so any prior decomposition (including a nullopt failure)
    // is still valid. Returns by-value to preserve the existing API.
    {
        auto it = termsCache_.find(a);
        if (it != termsCache_.end()) {
            ++termsHits_;
            return it->second;
        }
    }
    ++termsMisses_;

    const auto& p = get(a);

    // Constant polynomial: return single term with empty powers
    if (poly::is_constant(p)) {
        poly::Assignment empty(ctx_);
        poly::Value v = poly::evaluate(p, empty);
        if (!poly::is_rational(v)) {
            termsCache_.emplace(a, std::nullopt);
            return std::nullopt;
        }
        const poly::Rational& r = poly::as_rational(v);
        mpq_class c = *poly::detail::cast_to_gmp(&r);
        if (c.get_den() != 1) {
            termsCache_.emplace(a, std::nullopt);
            return std::nullopt;
        }
        std::vector<MonomialTerm> result{{c.get_num(), {}}};
        termsCache_.emplace(a, result);
        return result;
    }

    TermsTraverseData data;
    data.kernel = this;
    lp_polynomial_traverse(p.get_internal(), termsTraverseCallback, &data);

    if (data.failed) {
        termsCache_.emplace(a, std::nullopt);
        return std::nullopt;
    }
    termsCache_.emplace(a, data.terms);
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

PolynomialKernel::PseudoRemainderResult LibPolyKernel::pseudoRemainderWithScale(
    PolyId dividend, PolyId divisor, VarId mainVar) {

    auto remOpt = pseudoRemainder(dividend, divisor);
    if (!remOpt) {
        return {NullPoly, NullPoly, 0};
    }

    auto degDividend = degree(dividend, varName(mainVar));
    auto degDivisor  = degree(divisor, varName(mainVar));

    if (!degDivisor) {
        return {NullPoly, NullPoly, 0};
    }

    if (!degDividend) {
        // Dividend is constant in mainVar: reducing it modulo a polynomial in
        // mainVar leaves it unchanged, so the pseudo-remainder is the dividend.
        return {dividend, NullPoly, 0};
    }

    int k = *degDividend - *degDivisor + 1;
    if (k <= 0) {
        // deg(dividend, mainVar) < deg(divisor, mainVar): no reduction w.r.t.
        // mainVar is possible, so the pseudo-remainder w.r.t. mainVar is the
        // dividend itself. The plain pseudoRemainder above may reduce w.r.t. the
        // wrong main variable (libpoly's prem uses each operand's own largest
        // variable), producing a spurious 0 — this caused signAtTower to report
        // Sign::Zero for polynomials constant in the algebraic var (nra_092's
        // false witness x=1/2 satisfying x>=1).
        return {dividend, NullPoly, 0};
    }

    auto lcOpt = leadingCoefficient(divisor);
    if (!lcOpt) {
        return {*remOpt, NullPoly, 0};
    }

    // Check if libpoly's prem used the correct variable.
    // If the dividend's main variable is NOT mainVar, poly::prem may have
    // computed with respect to the wrong variable, producing an incorrect
    // remainder (often 0). In that case we recompute the pseudo-remainder
    // manually by iterating over terms.
    const auto& pp = get(dividend);
    auto it = nameToVar_.find(std::string(varName(mainVar)));
    if (it != nameToVar_.end()) {
        poly::Variable pv = varIdToPolyVar_[it->second];
        if (poly::main_variable(pp) != pv && *degDividend >= *degDivisor) {
            // Manual pseudo-remainder with respect to mainVar.
            PolyId current = dividend;
            for (int iter = 0; iter < 100; ++iter) {
                auto curDegOpt = degree(current, varName(mainVar));
                if (!curDegOpt || *curDegOpt < *degDivisor) break;

                // Extract leading coefficient w.r.t. mainVar from terms
                auto termsOpt = terms(current);
                if (!termsOpt) break;

                int maxDeg = -1;
                mpq_class lcCoeff(0);
                std::vector<std::pair<VarId, int>> lcPowers;
                for (const auto& term : *termsOpt) {
                    int varDeg = 0;
                    for (const auto& [vid, exp] : term.powers) {
                        if (vid == mainVar) {
                            varDeg = exp;
                            break;
                        }
                    }
                    if (varDeg > maxDeg) {
                        maxDeg = varDeg;
                        lcCoeff = term.coefficient;
                        lcPowers.clear();
                        for (const auto& [vid, exp] : term.powers) {
                            if (vid != mainVar) lcPowers.push_back({vid, exp});
                        }
                    }
                }
                if (maxDeg < *degDivisor) break;

                int d = maxDeg - *degDivisor;

                // scaledCurrent = lcDivisor * current
                PolyId scaledCurrent = mul(*lcOpt, current);

                // subtrahend = lcCurrent * var^d * divisor
                PolyId lcCurrent = mkConst(lcCoeff);
                for (const auto& [vid, exp] : lcPowers) {
                    lcCurrent = mul(lcCurrent, pow(mkVar(vid), exp));
                }
                PolyId varPow = pow(mkVar(mainVar), d);
                PolyId subtrahend = mul(lcCurrent, mul(varPow, divisor));

                current = sub(scaledCurrent, subtrahend);

                auto newDegOpt = degree(current, varName(mainVar));
                if (!newDegOpt) break;
                if (*newDegOpt >= maxDeg) {
                    // Degree did not decrease: stop to avoid infinite loop
                    break;
                }
            }
            // Build scale factor = lc(divisor)^k
            PolyId scaleFactor = mkOne();
            for (int i = 0; i < k; ++i) {
                scaleFactor = mul(scaleFactor, *lcOpt);
            }
            return {current, scaleFactor, k};
        }
    }

    PolyId scaleFactor = mkOne();
    for (int i = 0; i < k; ++i) {
        scaleFactor = mul(scaleFactor, *lcOpt);
    }

    return {*remOpt, scaleFactor, k};
}

std::optional<PolyId> LibPolyKernel::leadingCoefficient(PolyId p) {
    // S1b: hash-cons. Unary, deterministic given fixed construction-time main
    // variable. nullopt cached as NullPoly value (cache value space is disjoint
    // from key space, no collision risk).
    if (p == NullPoly) return std::nullopt;
    const uint64_t key = binOpKey(6, p, 0);
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) {
        ++binOpHits_;
        return it->second == NullPoly ? std::optional<PolyId>{} : std::optional<PolyId>{it->second};
    }
    ++binOpMisses_;
    const auto& pp = get(p);
    if (poly::is_constant(pp)) {
        binOpCache_.emplace(key, NullPoly);
        return std::nullopt;
    }
    try {
        poly::Polynomial lc = poly::leading_coefficient(pp);
        PolyId r = alloc(std::move(lc));
        binOpCache_.emplace(key, r);
        return r;
    } catch (...) {
        // Don't cache transient exceptions
        return std::nullopt;
    }
}

// Track C1 / Phase 1. Symbolic-modulus residue extraction. See
// PolynomialKernel.h for the API doc and modInvStep motivation.
//
// Implementation strategy: identify the (single) variable `v` the modulus
// is in, run a polynomial long-division using v as the main variable, and
// return the remainder when the modulus is monic in v (leading coefficient
// 1). Non-monic or multi-variable modulus → nullopt (caller falls
// through). pseudoRemainderWithScale is the existing primitive; for a monic
// divisor in v, the scale factor lc(divisor)^k is 1^k = 1 so the
// pseudo-remainder equals the true polynomial remainder. That property
// gives the soundness guarantee (poly ≡ r mod modulus over Z under any
// integer assignment to v).
std::optional<PolyId> LibPolyKernel::extractSymbolicResidue(PolyId poly, PolyId modulus) {
    if (poly == NullPoly || modulus == NullPoly) return std::nullopt;

    // The modulus must be non-constant and univariate. A constant modulus
    // belongs to the numeric path (ModularResidueReasoner step 8 Hensel).
    if (isConstant(modulus)) return std::nullopt;
    auto modVars = variables(modulus);
    if (modVars.size() != 1) return std::nullopt;  // Phase 1: monovariate only

    auto vidOpt = findVar(modVars[0]);
    if (!vidOpt) return std::nullopt;
    VarId v = *vidOpt;

    // The modulus must be monic in v: lc_v(modulus) = 1 (constant). Without
    // that, pseudoRemainder returns lc^k × residue rather than the true
    // residue, and we cannot soundly normalize the scaling out at the
    // polynomial level. Phase-1 fail-closed.
    auto lcOpt = leadingCoefficient(modulus);
    if (!lcOpt) return std::nullopt;
    if (!isConstant(*lcOpt)) return std::nullopt;
    if (toConstant(*lcOpt) != mpq_class(1)) return std::nullopt;

    // Compute the pseudo-remainder w.r.t. v. For monic divisor in v, this
    // is the actual polynomial remainder (deg_v(r) < deg_v(modulus)).
    auto res = pseudoRemainderWithScale(poly, modulus, v);
    if (res.remainder == NullPoly) return std::nullopt;
    // Defensive: confirm the scale factor is 1 (or nullopt, which the
    // wrapper uses to signal "no scale needed").
    if (res.scaleFactor != NullPoly) {
        if (!isConstant(res.scaleFactor)) return std::nullopt;
        if (toConstant(res.scaleFactor) != mpq_class(1)) return std::nullopt;
    }
    return res.remainder;
}

std::vector<PolyId> LibPolyKernel::pscChain(PolyId a, PolyId b, VarId v) {
    // Degenerate: a side with degree < 1 in v has no subresultant chain.
    // (degree() works for non-main variables too, via term inspection.)
    auto degA = degree(a, varName(v));
    auto degB = degree(b, varName(v));
    if (!degA || !degB || *degA < 1 || *degB < 1) {
        return {};
    }

    poly::Variable elimVar = resolvePolyVar(v);
    lp_variable_order_t* order = ctx_.get_variable_order();

    // --- Snapshot the current variable order so we can restore it. --------
    // Xolver leaves the libpoly order empty by default (main_variable is then
    // tie-broken by creation order), so this is normally a no-op snapshot, but
    // we restore exactly what was there to be robust against any future state.
    std::vector<lp_variable_t> saved;
    {
        const lp_variable_list_t* list = lp_variable_order_get_list(order);
        size_t n = lp_variable_list_size(list);
        saved.resize(n);
        if (n > 0) {
            lp_variable_list_copy_into(list, saved.data());
        }
    }

    // --- Install an order that makes v the TOP (main) variable. -----------
    // Collect every variable appearing in a or b except v, push them first
    // (any relative order among them is fine — they all stay below v), then
    // push v last so it becomes the highest / main variable.
    lp_variable_order_clear(order);
    std::set<lp_variable_t> pushed;
    auto pushOthers = [&](PolyId id) {
        for (const std::string& name : variables(id)) {
            auto vidOpt = findVar(name);
            if (!vidOpt) continue;
            if (*vidOpt == v) continue;
            lp_variable_t lv = resolvePolyVar(*vidOpt).get_internal();
            if (pushed.insert(lv).second) {
                lp_variable_order_push(order, lv);
            }
        }
    };
    pushOthers(a);
    pushOthers(b);
    lp_variable_order_push(order, elimVar.get_internal());

    auto restoreOrder = [&]() {
        lp_variable_order_clear(order);
        for (lp_variable_t lv : saved) {
            lp_variable_order_push(order, lv);
        }
    };

    // --- Re-order copies of a, b to the new order, then compute psc. ------
    // ensure_order rewrites the recursive representation so v is the top
    // variable; without this the precomputed pool_ polynomials keep their
    // construction-time ordering and psc would eliminate the wrong variable.
    std::vector<PolyId> result;
    try {
        lp_polynomial_t* rawA =
            lp_polynomial_new_copy(get(a).get_internal());
        lp_polynomial_t* rawB =
            lp_polynomial_new_copy(get(b).get_internal());
        lp_polynomial_ensure_order(rawA);
        lp_polynomial_ensure_order(rawB);
        poly::Polynomial pa(rawA);  // adopts ownership
        poly::Polynomial pb(rawB);

        // Defensive: both must now have v as their main variable, otherwise
        // psc would eliminate the wrong variable. (Can only fail if v does not
        // actually occur, which the degree guard above already excludes.)
        if (poly::main_variable(pa) != elimVar ||
            poly::main_variable(pb) != elimVar) {
            restoreOrder();
            return {};
        }

        std::vector<poly::Polynomial> chain = poly::psc(pa, pb);

        // poly::psc returns min(deg_v a, deg_v b)+1 entries; the determinant
        // reference returns exactly min entries (index j = psc_j, j<min). Drop
        // the trailing entry to keep the chains index-for-index aligned.
        size_t keep = chain.empty() ? 0 : chain.size() - 1;
        result.reserve(keep);
        for (size_t j = 0; j < keep; ++j) {
            result.push_back(alloc(std::move(chain[j])));
        }
    } catch (...) {
        restoreOrder();
        return {};
    }

    restoreOrder();
    return result;
}

PolyId LibPolyKernel::gcd(PolyId a, PolyId b) {
    // lp_polynomial_gcd is the FULL multivariate, content-aware gcd over the
    // recursive representation. Unlike resultant/psc (which eliminate a chosen
    // top variable), gcd does NOT depend on the variable order — it is the gcd
    // of a and b as elements of Z[vars]. So no order push/restore is needed.
    //
    // Sign/scale: libpoly returns a representative of the gcd in its integer
    // ring; the Lazard caller treats it up to a positive rational unit (and
    // re-verifies it via exactDivide), so the exact normalization is benign.
    //
    // S1b: hash-cons. Order-independent, deterministic → commutative cache fit.
    if (a == NullPoly || b == NullPoly) {
        try { return alloc(poly::gcd(get(a), get(b))); } catch (...) { return NullPoly; }
    }
    const PolyId lo = a < b ? a : b, hi = a < b ? b : a;
    const uint64_t key = binOpKey(5, lo, hi);
    auto it = binOpCache_.find(key);
    if (it != binOpCache_.end()) { ++binOpHits_; return it->second; }
    ++binOpMisses_;
    try {
        poly::Polynomial g = poly::gcd(get(a), get(b));
        PolyId r = alloc(std::move(g));
        binOpCache_.emplace(key, r);
        return r;
    } catch (...) {
        // Do NOT cache failures — could be transient (allocator OOM etc.)
        return NullPoly;
    }
}

std::vector<PolyId> LibPolyKernel::squareFreeFactors(PolyId a) {
    // poly::square_free_factors returns the non-constant square-free factors whose
    // product is the square-free part of `a` — i.e. their union of real roots is
    // exactly a's real-root set (multiplicity collapsed). Replacing a by these
    // factors in the CAC characterization is ROOT-PRESERVING (sound). On any
    // failure, fall back to {a} (conservative no-op — never drops roots).
    //
    // S1b: hash-cons by input PolyId. This is the HOT path for cas/sqrtmodinv —
    // SingleCellProjection.cpp:258 calls this per boundary, and the same
    // boundary recurs across cell-jump iterations. Vector-valued cache (each
    // entry stores the factor PolyIds, not the polynomials themselves).
    if (a == NullPoly) return {a};
    auto cIt = sqfFactorsCache_.find(a);
    if (cIt != sqfFactorsCache_.end()) { ++binOpHits_; return cIt->second; }
    ++binOpMisses_;
    std::vector<PolyId> out;
    try {
        std::vector<poly::Polynomial> facs = poly::square_free_factors(get(a));
        out.reserve(facs.size());
        for (auto& f : facs) {
            if (poly::is_constant(f)) continue;          // constants have no roots
            out.push_back(alloc(std::move(f)));
        }
        if (out.empty()) out.push_back(a);                // all-constant / degenerate ⇒ keep a
    } catch (...) {
        out = {a};
    }
    sqfFactorsCache_.emplace(a, out);                     // cache even the fallback (deterministic)
    return out;
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

} // namespace xolver

#endif // XOLVER_HAS_LIBPOLY
