#include "theory/arith/poly/RationalPolynomial.h"
#include <numeric>
#include <functional>

namespace nlcolver {

// ============================================================================
// Static helpers
// ============================================================================

MonomialKey RationalPolynomial::multiplyKeys(const MonomialKey& a,
                                              const MonomialKey& b) {
    MonomialKey result;
    size_t i = 0, j = 0;
    while (i < a.size() && j < b.size()) {
        if (a[i].first < b[j].first) {
            result.push_back(a[i++]);
        } else if (b[j].first < a[i].first) {
            result.push_back(b[j++]);
        } else {
            int exp = a[i].second + b[j].second;
            if (exp > 0) result.push_back({a[i].first, exp});
            ++i; ++j;
        }
    }
    while (i < a.size()) result.push_back(a[i++]);
    while (j < b.size()) result.push_back(b[j++]);
    return result;
}

MonomialKey RationalPolynomial::powKey(const MonomialKey& a, uint32_t n) {
    if (n == 0) return {};
    MonomialKey result;
    result.reserve(a.size());
    for (const auto& [var, exp] : a) {
        result.push_back({var, exp * static_cast<int>(n)});
    }
    return result;
}

// ============================================================================
// Construction helpers
// ============================================================================

RationalPolynomial RationalPolynomial::fromConstant(const mpq_class& c) {
    RationalPolynomial p;
    if (c != 0) p.terms_[{}] = c;
    return p;
}

RationalPolynomial RationalPolynomial::fromVar(VarId v, int exp,
                                               const mpq_class& coeff) {
    RationalPolynomial p;
    if (coeff != 0 && exp > 0) {
        p.terms_[{{v, exp}}] = coeff;
    }
    return p;
}

void RationalPolynomial::addTerm(const MonomialKey& key,
                                 const mpq_class& coeff) {
    if (coeff != 0) {
        terms_[key] += coeff;
    }
}

void RationalPolynomial::addConstant(const mpq_class& coeff) {
    if (coeff != 0) {
        terms_[{}] += coeff;
    }
}

void RationalPolynomial::addVar(VarId v, int exp, const mpq_class& coeff) {
    if (coeff != 0 && exp > 0) {
        terms_[{{v, exp}}] += coeff;
    }
}

// ============================================================================
// Queries
// ============================================================================

bool RationalPolynomial::isConstant() const {
    for (const auto& [key, coeff] : terms_) {
        (void)coeff;
        if (!key.empty()) return false;
    }
    return true;
}

mpq_class RationalPolynomial::constantValue() const {
    mpq_class result(0);
    for (const auto& [key, coeff] : terms_) {
        if (key.empty()) result += coeff;
    }
    return result;
}

// ============================================================================
// Algebraic operations
// ============================================================================

RationalPolynomial RationalPolynomial::operator+(
    const RationalPolynomial& other) const {
    RationalPolynomial result = *this;
    for (const auto& [key, coeff] : other.terms_) {
        result.terms_[key] += coeff;
    }
    result.normalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator-(
    const RationalPolynomial& other) const {
    RationalPolynomial result = *this;
    for (const auto& [key, coeff] : other.terms_) {
        result.terms_[key] -= coeff;
    }
    result.normalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator*(
    const RationalPolynomial& other) const {
    RationalPolynomial result;
    for (const auto& [k1, c1] : terms_) {
        for (const auto& [k2, c2] : other.terms_) {
            auto key = multiplyKeys(k1, k2);
            result.terms_[key] += c1 * c2;
        }
    }
    result.normalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator-() const {
    RationalPolynomial result = *this;
    for (auto& [key, coeff] : result.terms_) {
        (void)key;
        coeff = -coeff;
    }
    return result;
}

RationalPolynomial& RationalPolynomial::operator+=(
    const RationalPolynomial& other) {
    for (const auto& [key, coeff] : other.terms_) {
        terms_[key] += coeff;
    }
    normalize();
    return *this;
}

RationalPolynomial& RationalPolynomial::operator-=(
    const RationalPolynomial& other) {
    for (const auto& [key, coeff] : other.terms_) {
        terms_[key] -= coeff;
    }
    normalize();
    return *this;
}

RationalPolynomial& RationalPolynomial::operator*=(const mpq_class& scalar) {
    if (scalar == 0) {
        terms_.clear();
        return *this;
    }
    for (auto& [key, coeff] : terms_) {
        (void)key;
        coeff *= scalar;
    }
    return *this;
}

RationalPolynomial RationalPolynomial::pow(uint32_t n) const {
    if (n == 0) return fromConstant(mpq_class(1));
    if (n == 1) return *this;

    // Binary exponentiation
    RationalPolynomial result = fromConstant(mpq_class(1));
    RationalPolynomial base = *this;
    uint32_t exp = n;
    while (exp > 0) {
        if (exp & 1) result = result * base;
        base = base * base;
        exp >>= 1;
    }
    return result;
}

// ============================================================================
// Normalization
// ============================================================================

void RationalPolynomial::normalize() {
    for (auto it = terms_.begin(); it != terms_.end(); ) {
        if (it->second == 0) {
            it = terms_.erase(it);
        } else {
            ++it;
        }
    }
    // Keys are kept sorted by std::map.
    // Variable order inside each key is maintained by multiplyKeys/powKey.
}

// ============================================================================
// Conversion to primitive integer polynomial
// ============================================================================

RationalPolynomial::NormalizedResult
RationalPolynomial::toPrimitiveInteger(PolynomialKernel& kernel) const {
    if (terms_.empty()) {
        PolyId zero = kernel.mkZero();
        return {zero, mpq_class(1)};
    }

    // Step 1: LCM of all denominators
    mpz_class D = 1;
    for (const auto& [key, coeff] : terms_) {
        (void)key;
        mpz_class den = coeff.get_den();
        if (den > 1) {
            mpz_class tmp;
            mpz_lcm(tmp.get_mpz_t(), D.get_mpz_t(), den.get_mpz_t());
            D = tmp;
        }
    }

    // Step 2: Scale to integer coefficients
    std::map<MonomialKey, mpz_class> intTerms;
    for (const auto& [key, coeff] : terms_) {
        mpz_class num = coeff.get_num();
        mpz_class den = coeff.get_den();
        mpz_class a = num * (D / den);
        if (a != 0) {
            auto it = intTerms.find(key);
            if (it != intTerms.end()) {
                it->second += a;
            } else {
                intTerms[key] = a;
            }
        }
    }

    // Remove zeros
    for (auto it = intTerms.begin(); it != intTerms.end(); ) {
        if (it->second == 0) {
            it = intTerms.erase(it);
        } else {
            ++it;
        }
    }

    if (intTerms.empty()) {
        PolyId zero = kernel.mkZero();
        return {zero, mpq_class(1)};
    }

    // Step 3: GCD of absolute coefficients
    mpz_class g = 0;
    for (const auto& [key, coeff] : intTerms) {
        (void)key;
        mpz_class absCoeff = coeff >= 0 ? coeff : -coeff;
        if (g == 0) {
            g = absCoeff;
        } else {
            mpz_class tmp;
            mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), absCoeff.get_mpz_t());
            g = tmp;
        }
        if (g == 1) break;
    }

    // Step 4: Divide by GCD -> primitive coefficients
    for (auto& [key, coeff] : intTerms) {
        (void)key;
        coeff /= g;
    }

    // Step 5: Build PolyId via divide-and-conquer to avoid O(N^2)
    // linear accumulation.  Each term is built independently, then
    // merged pairwise so intermediate polynomials are balanced.
    struct Item { MonomialKey key; mpz_class coeff; };
    std::vector<Item> items;
    items.reserve(intTerms.size());
    for (auto& [key, coeff] : intTerms) {
        items.push_back({std::move(const_cast<MonomialKey&>(key)), std::move(coeff)});
    }
    // Release the map early
    intTerms.clear();

    auto build = [&](auto&& self, size_t l, size_t r) -> PolyId {
        if (l == r) {
            const auto& it = items[l];
            PolyId termPoly = kernel.mkConst(mpq_class(it.coeff, 1));
            if (termPoly == NullPoly) return NullPoly;
            for (const auto& [varId, exp] : it.key) {
                PolyId varPoly = kernel.mkVar(varId);
                if (exp == 1) {
                    termPoly = kernel.mul(termPoly, varPoly);
                } else {
                    termPoly = kernel.mul(termPoly,
                        kernel.pow(varPoly, static_cast<uint32_t>(exp)));
                }
                if (termPoly == NullPoly) return NullPoly;
            }
            return termPoly;
        }
        size_t m = l + (r - l) / 2;
        PolyId left  = self(self, l, m);
        if (left == NullPoly) return NullPoly;
        PolyId right = self(self, m + 1, r);
        if (right == NullPoly) return NullPoly;
        return kernel.add(left, right);
    };

    PolyId result = build(build, 0, items.size() - 1);
    if (result == NullPoly) return {};

    mpq_class scale(g, D);
    scale.canonicalize();
    return {result, scale};
}

// ============================================================================
// Reconstruction from PolyId
// ============================================================================

std::optional<RationalPolynomial> RationalPolynomial::fromPolyId(
    PolyId p, const PolynomialKernel& kernel) {
    auto termsOpt = kernel.terms(p);
    if (!termsOpt) return std::nullopt;

    RationalPolynomial rp;
    for (const auto& term : *termsOpt) {
        rp.addTerm(term.powers, mpq_class(term.coefficient));
    }
    rp.normalize();
    return rp;
}

// ============================================================================
// CDCAC V1 extensions
// ============================================================================

bool RationalPolynomial::contains(VarId v) const {
    for (const auto& [key, coeff] : terms_) {
        (void)coeff;
        for (const auto& [varId, exp] : key) {
            if (varId == v && exp > 0) return true;
        }
    }
    return false;
}

int RationalPolynomial::degree(VarId v) const {
    int d = -1;
    for (const auto& [key, coeff] : terms_) {
        (void)coeff;
        int termDeg = 0;
        for (const auto& [varId, exp] : key) {
            if (varId == v) termDeg = exp;
        }
        d = std::max(d, termDeg);
    }
    return d;
}

std::vector<RationalPolynomial> RationalPolynomial::coefficients(VarId v) const {
    int d = degree(v);
    if (d < 0) return {};

    std::vector<RationalPolynomial> result(d + 1);
    for (const auto& [key, coeff] : terms_) {
        int exp = 0;
        MonomialKey remaining;
        for (const auto& [varId, e] : key) {
            if (varId == v) {
                exp = e;
            } else {
                remaining.push_back({varId, e});
            }
        }
        result[exp].terms_[remaining] += coeff;
    }
    for (auto& rp : result) {
        rp.normalize();
    }
    return result;
}

RationalPolynomial RationalPolynomial::leadingCoefficient(VarId v) const {
    int d = degree(v);
    if (d < 0) return fromConstant(mpq_class(0));

    RationalPolynomial result;
    for (const auto& [key, coeff] : terms_) {
        int exp = 0;
        MonomialKey remaining;
        for (const auto& [varId, e] : key) {
            if (varId == v) {
                exp = e;
            } else {
                remaining.push_back({varId, e});
            }
        }
        if (exp == d) {
            result.terms_[remaining] += coeff;
        }
    }
    result.normalize();
    return result;
}

RationalPolynomial RationalPolynomial::derivative(VarId v) const {
    RationalPolynomial result;
    for (const auto& [key, coeff] : terms_) {
        int exp = 0;
        MonomialKey remaining;
        for (const auto& [varId, e] : key) {
            if (varId == v) {
                exp = e;
            } else {
                remaining.push_back({varId, e});
            }
        }
        if (exp > 0) {
            mpq_class newCoeff = coeff * mpq_class(exp);
            if (exp == 1) {
                result.terms_[remaining] += newCoeff;
            } else {
                MonomialKey newKey = remaining;
                auto it = std::lower_bound(newKey.begin(), newKey.end(), v,
                    [](const auto& p, VarId vid) { return p.first < vid; });
                newKey.insert(it, {v, exp - 1});
                result.terms_[newKey] += newCoeff;
            }
        }
    }
    result.normalize();
    return result;
}

RationalPolynomial RationalPolynomial::pseudoRemainder(VarId v, const RationalPolynomial& divisor) const {
    int degP = degree(v);
    int degQ = divisor.degree(v);

    if (degP < degQ) return *this;
    if (degQ < 0) return *this; // divisor is zero

    auto pCoeffs = coefficients(v);
    auto qCoeffs = divisor.coefficients(v);

    RationalPolynomial lcQ = qCoeffs[degQ];
    int k = degP - degQ + 1;

    std::vector<RationalPolynomial> rem = pCoeffs;

    for (int step = 0; step < k; ++step) {
        int remDeg = -1;
        for (int i = static_cast<int>(rem.size()) - 1; i >= 0; --i) {
            if (!rem[i].isZero()) {
                remDeg = i;
                break;
            }
        }
        if (remDeg < degQ) break;

        // r = lc(q) * r
        for (auto& c : rem) {
            c = c * lcQ;
        }

        // r = r - lc(r) * q * x^(remDeg - degQ)
        RationalPolynomial lcRem = rem[remDeg];
        int shift = remDeg - degQ;
        for (size_t j = 0; j < qCoeffs.size(); ++j) {
            int idx = shift + static_cast<int>(j);
            if (idx >= 0 && idx < static_cast<int>(rem.size())) {
                rem[idx] = rem[idx] - lcRem * qCoeffs[j];
            }
        }
    }

    // Reconstruct remainder polynomial
    RationalPolynomial result;
    for (size_t i = 0; i < rem.size(); ++i) {
        if (rem[i].isZero()) continue;
        for (const auto& [key, coeff] : rem[i].terms()) {
            MonomialKey newKey = key;
            auto it = std::lower_bound(newKey.begin(), newKey.end(), v,
                [](const auto& pair, VarId vid) { return pair.first < vid; });
            newKey.insert(it, {v, static_cast<int>(i)});
            result.addTerm(newKey, coeff);
        }
    }
    result.normalize();
    return result;
}

std::set<VarId> RationalPolynomial::variables() const {
    std::set<VarId> result;
    for (const auto& [key, coeff] : terms_) {
        (void)coeff;
        for (const auto& [varId, exp] : key) {
            if (exp > 0) result.insert(varId);
        }
    }
    return result;
}

int RationalPolynomial::highestVariableLevel(const std::vector<VarId>& varOrder) const {
    int highest = -1;
    auto vars = variables();
    for (VarId v : vars) {
        for (size_t i = 0; i < varOrder.size(); ++i) {
            if (varOrder[i] == v) {
                highest = std::max(highest, static_cast<int>(i));
                break;
            }
        }
    }
    return highest;
}

RationalPolynomial RationalPolynomial::substituteRational(VarId v, const mpq_class& q) const {
    RationalPolynomial result;
    for (const auto& [key, coeff] : terms_) {
        mpq_class factor(1);
        MonomialKey remaining;
        for (const auto& [varId, exp] : key) {
            if (varId == v) {
                // q^exp
                mpq_class qe = q;
                for (int i = 1; i < exp; ++i) qe *= q;
                factor *= qe;
            } else {
                remaining.push_back({varId, exp});
            }
        }
        result.terms_[remaining] += coeff * factor;
    }
    result.normalize();
    return result;
}

PolyId RationalPolynomial::toPolyId(PolynomialKernel& kernel) const {
    if (terms_.empty()) return kernel.mkZero();
    auto norm = toPrimitiveInteger(kernel);
    if (!norm.ok()) return NullPoly;
    return norm.poly;
}

// ============================================================================
// V2-1: content and primitive part
// ============================================================================

mpq_class RationalPolynomial::content(VarId v) const {
    if (terms_.empty()) return mpq_class(0);

    auto coeffs = coefficients(v);
    if (coeffs.empty()) return mpq_class(0);

    // Skip zero coefficients and check if all non-zero coefficients are constant
    mpq_class result = mpq_class(0);
    bool allConstant = true;
    bool foundNonZero = false;

    for (const auto& c : coeffs) {
        if (c.isZero()) continue;
        if (!c.isConstant()) {
            allConstant = false;
            break;
        }
        mpq_class val = c.constantValue();
        if (!foundNonZero) {
            result = val;
            foundNonZero = true;
        } else {
            // GCD of two rationals a/b and c/d:
            // = gcd(a*d, c*b) / (b*d)
            mpz_class num1 = result.get_num() * val.get_den();
            mpz_class num2 = val.get_num() * result.get_den();
            mpz_class den = result.get_den() * val.get_den();
            mpz_class g;
            mpz_gcd(g.get_mpz_t(), num1.get_mpz_t(), num2.get_mpz_t());
            result = mpq_class(g, den);
        }
    }

    if (!foundNonZero) return mpq_class(0);
    if (!allConstant) return mpq_class(1);  // multivariate: primitive by default
    return result;
}

RationalPolynomial RationalPolynomial::primitivePart(VarId v) const {
    mpq_class c = content(v);
    if (c == 0 || c == 1) return *this;
    RationalPolynomial result = *this;
    for (auto& [key, coeff] : result.terms_) {
        coeff /= c;
    }
    result.normalize();
    return result;
}

} // namespace nlcolver
