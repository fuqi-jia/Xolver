#include "theory/arith/poly/RationalPolynomial.h"
#include <algorithm>
#include <functional>
#include <numeric>

namespace xolver {

// Canonicalize a MonomialKey so map lookups behave correctly:
//   * sort by VarId ascending (lex-canonical form used elsewhere),
//   * merge duplicate VarId entries by summing exponents,
//   * drop entries whose final exponent is <= 0 (var^0 = 1, var^neg disallowed).
// Returning a fresh vector keeps the function copy-friendly.
static MonomialKey canonicalizeMonomialKey(MonomialKey key) {
    if (key.size() > 1) {
        std::sort(key.begin(), key.end(),
            [](const auto& a, const auto& b) { return a.first < b.first; });
        // Merge duplicates produced by callers that listed the same VarId twice.
        // SmallVector has no erase(first,last), so build a fresh canonical key
        // (same semantics: sort by VarId asc, merge dup VarId by summing exp,
        // drop exp <= 0).
        MonomialKey merged;
        for (auto read = key.begin(); read != key.end(); ) {
            auto next = read + 1;
            int exp = read->second;
            while (next != key.end() && next->first == read->first) {
                exp += next->second;
                ++next;
            }
            if (exp > 0) {
                merged.push_back({read->first, exp});
            }
            read = next;
        }
        return merged;
    } else if (key.size() == 1 && key[0].second <= 0) {
        key.clear();
    }
    return key;
}

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
    if (coeff == 0) return;
    // Defensive canonicalization: callers (e.g. fromPolyId pulling terms
    // through the libpoly traversal callback, or GcdEngine reconstructing
    // an exact-division quotient) can pass keys that are unsorted or carry
    // an explicit var^0 factor. Inserting them as-is would create distinct
    // map entries for what is mathematically the same monomial — silently
    // breaking term-by-term polynomial equality (e.g. the verification
    // multiplication in GcdEngine::gcdCandidateBySubresultant would fail
    // for any case requiring canonical compare).
    MonomialKey canonical = canonicalizeMonomialKey(key);
    terms_[std::move(canonical)] += coeff;
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
    // Hot build: append all terms then canonicalize once (O(m log m)) rather
    // than repeated sorted inserts (O(n^2)). canonicalize() sorts, merges
    // duplicate keys by += and strips zero coefficients — identical canonical
    // result to the old terms_[key] += coeff loop.
    RationalPolynomial result;
    result.terms_.reserve(terms_.size() + other.terms_.size());
    for (const auto& [key, coeff] : terms_) {
        result.terms_.append(key, coeff);
    }
    for (const auto& [key, coeff] : other.terms_) {
        result.terms_.append(key, coeff);
    }
    result.terms_.canonicalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator-(
    const RationalPolynomial& other) const {
    RationalPolynomial result;
    result.terms_.reserve(terms_.size() + other.terms_.size());
    for (const auto& [key, coeff] : terms_) {
        result.terms_.append(key, coeff);
    }
    for (const auto& [key, coeff] : other.terms_) {
        result.terms_.append(key, -coeff);
    }
    result.terms_.canonicalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator*(
    const RationalPolynomial& other) const {
    RationalPolynomial result;
    result.terms_.reserve(terms_.size() * other.terms_.size());
    for (const auto& [k1, c1] : terms_) {
        for (const auto& [k2, c2] : other.terms_) {
            result.terms_.append(multiplyKeys(k1, k2), c1 * c2);
        }
    }
    result.terms_.canonicalize();
    return result;
}

RationalPolynomial RationalPolynomial::operator-() const {
    // terms_ exposes only const iteration; rebuild with negated coefficients.
    // Keys are already canonical and stay sorted/unique under negation, so
    // append preserves order; canonicalize() re-establishes the invariant
    // cheaply (no zeros introduced by negation of nonzero coeffs).
    RationalPolynomial result;
    result.terms_.reserve(terms_.size());
    for (const auto& [key, coeff] : terms_) {
        result.terms_.append(key, -coeff);
    }
    result.terms_.canonicalize();
    return result;
}

RationalPolynomial& RationalPolynomial::operator+=(
    const RationalPolynomial& other) {
    // terms_ is already canonical; append other's terms and re-canonicalize
    // once (sort+merge+strip) — same canonical result as repeated terms_[k]+=c.
    terms_.reserve(terms_.size() + other.terms_.size());
    for (const auto& [key, coeff] : other.terms_) {
        terms_.append(key, coeff);
    }
    terms_.canonicalize();
    return *this;
}

RationalPolynomial& RationalPolynomial::operator-=(
    const RationalPolynomial& other) {
    terms_.reserve(terms_.size() + other.terms_.size());
    for (const auto& [key, coeff] : other.terms_) {
        terms_.append(key, -coeff);
    }
    terms_.canonicalize();
    return *this;
}

RationalPolynomial& RationalPolynomial::operator*=(const mpq_class& scalar) {
    if (scalar == 0) {
        terms_.clear();
        return *this;
    }
    // terms_ exposes only const iteration; rebuild with scaled coefficients.
    // Scaling by a nonzero scalar preserves keys/order and introduces no zeros,
    // so canonical form is preserved.
    FlatMonomialMap<mpq_class> scaled;
    scaled.reserve(terms_.size());
    for (const auto& [key, coeff] : terms_) {
        scaled.append(key, coeff * scalar);
    }
    scaled.canonicalize();
    terms_ = std::move(scaled);
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
    // FlatMonomialMap::canonicalize() sorts entries by key, merges duplicate
    // keys by +=, and strips zero-coefficient entries — exactly the old
    // normalize semantics (the std::map already kept keys sorted; this also
    // tolerates any unsorted/duplicate entries from append-based builds).
    terms_.canonicalize();
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
    // S2 (P6) — driver-level memoization. T3 showed the SAME RP enters this
    // function multiple times per session (step-0/step-1 of each CAC cell,
    // squarefree call sites). The kernel's tpiCache (default no-op base,
    // active on LibPolyKernel) returns the cached NormalizedResult and skips
    // the LCM/GCD/Item-build/divide-and-conquer driver entirely.
    if (auto cached = kernel.tpiCacheLookup(*this)) {
        return {cached->first, cached->second};
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

    // Step 2: Scale to integer coefficients. terms_ is canonical (unique sorted
    // keys, no zero coeffs), so build the item list DIRECTLY — no intermediate
    // std::map<MonomialKey,...> / dedup / zero-removal is needed (it would be a
    // redundant std::map<heap-vector,...>, the very pattern this refactor kills).
    // Order is preserved: terms_ iterates in the same canonical lex order.
    struct Item { MonomialKey key; mpz_class coeff; };
    std::vector<Item> items;
    items.reserve(terms_.size());
    for (const auto& [key, coeff] : terms_) {
        mpz_class a = coeff.get_num() * (D / coeff.get_den());
        if (a != 0) items.push_back({key, std::move(a)});
    }

    if (items.empty()) {
        PolyId zero = kernel.mkZero();
        return {zero, mpq_class(1)};
    }

    // Step 3: GCD of absolute coefficients
    mpz_class g = 0;
    for (const auto& it : items) {
        mpz_class absCoeff = it.coeff >= 0 ? it.coeff : -it.coeff;
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
    for (auto& it : items) it.coeff /= g;

    // Step 5: Build the integer-coefficient PolyId in ONE pool allocation via the
    // kernel's batch builder. The previous in-place divide-and-conquer routed each
    // monomial (mkConst/mkVar/mul/pow) and each pairwise merge (add) through the
    // kernel, and a pooling/hash-consing backend (LibPolyKernel) interns every one
    // of those ~O(N) intermediates FOREVER — a 45k-term matrix-closure poly thus
    // leaked ~10^5 libpoly trees and OOM'd at 6 GB. mkFromMonomials performs the
    // same balanced sum over LOCAL (RAII) polynomials, so only the final result is
    // pooled and peak memory is O(N).
    std::vector<PolynomialKernel::MonomialTerm> mts;
    mts.reserve(items.size());
    for (auto& it : items) {
        PolynomialKernel::MonomialTerm mt;
        mt.coefficient = std::move(it.coeff);
        mt.powers.reserve(it.key.size());
        for (const auto& [varId, exp] : it.key)
            mt.powers.emplace_back(varId, static_cast<int>(exp));
        mts.push_back(std::move(mt));
    }
    PolyId result = kernel.mkFromMonomials(mts);
    if (result == NullPoly) return {};

    mpq_class scale(g, D);
    scale.canonicalize();
    kernel.tpiCacheStore(*this, result, scale);   // S2 — memoize for future calls
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
        // kernel terms expose powers as std::vector; build a MonomialKey
        // (SmallVector) from it for addTerm.
        MonomialKey key(term.powers.begin(), term.powers.end());
        rp.addTerm(key, mpq_class(term.coefficient));
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
                // SmallVector has no insert(); build a fresh sorted key with
                // {v, exp-1} placed at its VarId-ascending position so the
                // operator[] binary search stays canonical.
                MonomialKey newKey;
                newKey.reserve(remaining.size() + 1);
                bool inserted = false;
                for (const auto& pe : remaining) {
                    if (!inserted && v < pe.first) {
                        newKey.push_back({v, exp - 1});
                        inserted = true;
                    }
                    newKey.push_back(pe);
                }
                if (!inserted) newKey.push_back({v, exp - 1});
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

        // Capture the pre-multiplication leading coefficient. After scaling
        // rem by lc(q), the new leading coefficient is lc(q)*originalLc;
        // the correct pseudo-remainder step subtracts originalLc*q (not the
        // post-multiplication coefficient), giving cancellation when lc(q)
        // is non-constant in v. Reading lcRem after the multiplication
        // (the previous behaviour) caused the degree to never drop for
        // polynomials whose leading coefficient depends on other variables.
        RationalPolynomial lcRem = rem[remDeg];

        // r = lc(q) * r
        for (auto& c : rem) {
            c = c * lcQ;
        }

        // r = r - originalLc * q * x^(remDeg - degQ)
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
            // SmallVector has no insert(); append {v, i} and let addTerm's
            // canonicalizeMonomialKey re-sort/merge (i==0 -> exp 0 dropped).
            MonomialKey newKey = key;
            newKey.push_back({v, static_cast<int>(i)});
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

RationalPolynomial RationalPolynomial::substitute(VarId v,
                                                  const RationalPolynomial& expr) const {
    RationalPolynomial result;
    for (const auto& [key, coeff] : terms_) {
        int ev = 0;
        MonomialKey rest;
        for (const auto& [varId, exp] : key) {
            if (varId == v) ev = exp;
            else rest.push_back({varId, exp});
        }
        // term = coeff * (rest monomial) * expr^ev
        RationalPolynomial term = RationalPolynomial::fromConstant(coeff);
        if (!rest.empty()) {
            RationalPolynomial restPoly;
            restPoly.addTerm(rest, mpq_class(1));
            term = term * restPoly;
        }
        if (ev > 0) {
            term = term * expr.pow(static_cast<uint32_t>(ev));
        }
        result += term;
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
    // terms_ exposes only const iteration; rebuild dividing each coeff by c.
    // Dividing by a nonzero content preserves keys/order, introduces no zeros.
    RationalPolynomial result;
    result.terms_.reserve(terms_.size());
    for (const auto& [key, coeff] : terms_) {
        result.terms_.append(key, coeff / c);
    }
    result.terms_.canonicalize();
    return result;
}

} // namespace xolver
