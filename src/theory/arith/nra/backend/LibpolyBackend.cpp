#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/preprocess/SquarefreeEngine.h"
#include "theory/arith/nra/projection/LocalProjection.h"   // resultant()
#include "theory/arith/nra/valuation/TowerRootIsolation.h"     // towerNorm, TowerContext
#include "theory/arith/nra/valuation/RootMembershipOracle.h"   // lazardRootMembership
#include "theory/arith/nra/valuation/LazardValuationEngine.h"  // lazardEvaluateToUnivariate [H3]
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/LibPolyKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "util/EnvParam.h"   // XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS firewall
#include <algorithm>
#include <functional>

#include <iostream>
#include <map>
#include <unordered_set>
#include <csignal>
#include <csetjmp>

#ifdef XOLVER_HAS_LIBPOLY
#include <polyxx.h>
#endif

namespace {

// Crash-recovery for libpoly's lp_polynomial_roots_isolate, which can
// SIGSEGV on nested algebraic coefficients.  We use sigsetjmp/siglongjmp
// to return gracefully instead of crashing the whole process.
static std::sig_atomic_t g_libpolyCrashRecoveryActive = 0;
static sigjmp_buf g_libpolyJmpBuf;
static void (*g_oldSegvHandler)(int) = nullptr;
static void (*g_oldFpeHandler)(int) = nullptr;

static void libpolyCrashHandler(int sig) {
    if (g_libpolyCrashRecoveryActive) {
        siglongjmp(g_libpolyJmpBuf, sig);
    }
    // Not inside protected zone — chain to previous handler.
    if (sig == SIGSEGV && g_oldSegvHandler) {
        g_oldSegvHandler(sig);
    } else if (sig == SIGFPE && g_oldFpeHandler) {
        g_oldFpeHandler(sig);
    }
}

} // anonymous namespace

namespace xolver {

LibpolyBackend::LibpolyBackend(PolynomialKernel* kernel)
    : kernel_(kernel) {
#ifdef XOLVER_HAS_LIBPOLY
    libKernel_ = dynamic_cast<LibPolyKernel*>(kernel);
#endif
}

UniPolyId LibpolyBackend::allocUni(std::vector<mpz_class> coeffs) {
    UniPolyId id = static_cast<UniPolyId>(uniPool_.size());
    uniPool_.push_back(std::move(coeffs));
    return id;
}

const std::vector<mpz_class>& LibpolyBackend::getUni(UniPolyId id) const {
    return uniPool_[id];
}

#ifdef XOLVER_HAS_LIBPOLY
namespace {
// ---- libpoly heap-corruption firewall -------------------------------------
// Root cause (gdb-verified 2026-06-03): when libpoly's isolate_real_roots / sgn
// substitutes a large coordinate into a high-degree term, it builds multi-
// megabit rational coefficients; GMP overflows an internal size field and
// free()s a bogus (stack-region) pointer => glibc SIGABRT "double free or
// corruption". This is NOT a SIGSEGV, so the sigsetjmp recovery harness below
// cannot catch it. The crash lives in functions SHARED with CDCAC, so the only
// sound remedy is PREVENTION: refuse to hand libpoly an input whose substituted
// coefficients would exceed a generous magnitude ceiling, and bail as
// crashOccurred / Sign::Unknown (callers treat that as inconclusive => Unknown,
// never as "0 roots" / sign-invariant). Healthy CAD stays orders of magnitude
// below the ceiling (NRA reg unchanged); only pathological blowups degrade to
// Unknown instead of crashing. Ceiling tunable via the env::param registry.
long fwZbits(const mpz_class& z) {
    return z == 0 ? 0L : static_cast<long>(mpz_sizeinbase(z.get_mpz_t(), 2));
}
long fwMaxCoeffBits(const std::vector<mpz_class>& coeffs) {
    long m = 0;
    for (const auto& c : coeffs) m = std::max(m, fwZbits(c));
    return m;
}
long fwCapBits() {
    static const long cap = [] {
        int v = env::paramInt("XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS", 262144);
        return v > 0 ? static_cast<long>(v) : 262144L;  // <=0 => default (never silently disable)
    }();
    return cap;
}
bool fwTrips(long estBits, const char* where) {
    if (estBits <= fwCapBits()) return false;
    static const bool diag = std::getenv("XOLVER_NRA_LIBPOLY_FIREWALL_DIAG") != nullptr;
    if (diag) {
        std::cerr << "[LIBPOLY-FIREWALL] refuse " << where << " est=" << estBits
                  << "b > cap=" << fwCapBits() << "b (heap-corruption guard)\n";
    }
    return true;
}
// Upper bound on the bit-magnitude of the coefficients libpoly will materialize
// when it substitutes `sample` into `p`: sum over sampled vars of
// degree_v(p) * magnitudeBits(value_v). Over-estimate => fail safe (fire early).
long fwSubstitutedBits(const LibpolyBackend& be, const PolynomialKernel& kernel,
                       PolyId p, const SamplePoint& sample) {
    long total = 0;
    for (size_t i = 0; i < sample.numVars(); ++i) {
        const std::string vname(kernel.varName(sample.varOrder[i]));
        auto d = kernel.degree(p, vname);
        if (!d || *d <= 0) continue;
        const RealAlg& val = sample.values[i];
        long mbits = 0;
        if (val.isRational()) {
            mbits = std::max(fwZbits(val.rational.get_num()), fwZbits(val.rational.get_den()));
        } else if (val.isAlgebraic()) {
            mbits = std::max(mbits, std::max(fwZbits(val.root.lower.get_num()),
                                             fwZbits(val.root.lower.get_den())));
            mbits = std::max(mbits, std::max(fwZbits(val.root.upper.get_num()),
                                             fwZbits(val.root.upper.get_den())));
            if (val.root.definingPoly != NullUniPolyId)
                mbits = std::max(mbits, fwMaxCoeffBits(be.getUni(val.root.definingPoly)));
        }
        total += static_cast<long>(*d) * mbits;
    }
    return total;
}
} // namespace
#endif // XOLVER_HAS_LIBPOLY

RootSet LibpolyBackend::isolateRealRoots(UniPolyId p) {
#ifndef XOLVER_HAS_LIBPOLY
    (void)p;
    return RootSet{};
#else
    if (!libKernel_) return RootSet{};

    // V2-2: compute squarefree part before isolation
    SquarefreeEngine sqf(*this);
    auto sqfResult = sqf.compute(p);
    UniPolyId polyToIsolate = sqfResult.ok() ? sqfResult.squarefree : p;

    const auto& coeffs = getUni(polyToIsolate);
#ifndef NDEBUG
    std::cerr << "[CDCAC]       isolateRealRoots: polyToIsolate id=" << polyToIsolate << " coeffs=";
    for (auto c : coeffs) std::cerr << c.get_str() << " ";
    std::cerr << std::endl;
#endif
    if (coeffs.empty()) return RootSet{};

    // Handle linear polynomials exactly to avoid libpoly returning loose
    // isolating intervals (e.g. [-1/8, 0] for 8*y+1 where root is -1/8).
    if (coeffs.size() == 2) {
        mpq_class a(coeffs[0]);
        mpq_class b(coeffs[1]);
        if (a != 0) {
            RootSet result;
            result.roots.push_back(RealAlg::fromRational(-b / a));
            return result;
        }
    }

    // Heap-corruption firewall: a univariate polynomial with multi-Kbit integer
    // coefficients explodes libpoly's exact-rational interval arithmetic
    // (rational_interval_pow → multi-megabit GMP rationals → corrupt free; see
    // firewall note above). Such inputs are doubly-exponential and infeasible
    // regardless; bail as crashOccurred so callers treat it as inconclusive
    // (→ Unknown), NEVER as "0 roots". Refusing here keeps libpoly's context
    // pristine (no mid-computation state to corrupt).
    if (fwTrips(fwMaxCoeffBits(coeffs), "isolateRealRoots(uni)")) {
        RootSet r; r.crashOccurred = true; return r;
    }

    // Convert coefficients (high-to-low) to libpoly format (low-to-high)
    std::vector<poly::Integer> lpCoeffs;
    lpCoeffs.reserve(coeffs.size());
    for (auto it = coeffs.rbegin(); it != coeffs.rend(); ++it) {
        lpCoeffs.emplace_back(*it);
    }

    poly::UPolynomial up(lpCoeffs);
    std::vector<poly::AlgebraicNumber> roots = poly::isolate_real_roots(up);

    RootSet result;
    result.roots.reserve(roots.size());

    for (size_t i = 0; i < roots.size(); ++i) {
        const auto& r = roots[i];
        const poly::DyadicRational& lo = poly::get_lower_bound(r);
        const poly::DyadicRational& hi = poly::get_upper_bound(r);

        poly::Integer loNumInt = poly::numerator(lo);
        poly::Integer loDenInt = poly::denominator(lo);
        poly::Integer hiNumInt = poly::numerator(hi);
        poly::Integer hiDenInt = poly::denominator(hi);
        mpz_class loNum = *poly::detail::cast_to_gmp(&loNumInt);
        mpz_class loDen = *poly::detail::cast_to_gmp(&loDenInt);
        mpz_class hiNum = *poly::detail::cast_to_gmp(&hiNumInt);
        mpz_class hiDen = *poly::detail::cast_to_gmp(&hiDenInt);

        mpq_class lowerQ(loNum, loDen);
        mpq_class upperQ(hiNum, hiDen);

        // P2a-1: canonicalize rational roots (single-point isolating interval)
        if (lowerQ == upperQ) {
            mpq_class val = evalUniAtRational(coeffs, lowerQ);
            if (val == 0) {
                result.roots.push_back(RealAlg::fromRational(lowerQ));
                continue;
            }
        }

        AlgebraicRoot ar;
        // V2-2: definingPoly is the squarefree polynomial
        ar.definingPoly = polyToIsolate;
        ar.rootIndex = static_cast<int>(i);
        ar.lower = lowerQ;
        ar.upper = upperQ;

        result.roots.push_back(RealAlg::fromAlgebraic(std::move(ar)));
    }

    return result;
#endif
}

#ifdef XOLVER_HAS_LIBPOLY
static std::optional<poly::DyadicRational> mpqToDyadicRational(const mpq_class& q) {
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();
    if (den < 0) { num = -num; den = -den; }

    int n = 0;
    mpz_class temp = den;
    while (temp > 1) {
        if (temp % 2 != 0) {
            return std::nullopt;
        }
        temp /= 2;
        ++n;
    }

    lp_dyadic_rational_t dr;
    lp_dyadic_rational_construct(&dr);
    mpz_set(&dr.a, num.get_mpz_t());
    dr.n = static_cast<unsigned long>(n);
    poly::DyadicRational result(&dr);
    lp_dyadic_rational_destruct(&dr);
    return result;
}

static std::optional<poly::AlgebraicNumber> algebraicRootToPolyAlg(
    const AlgebraicRoot& ar,
    const std::vector<mpz_class>& coeffs) {
    if (ar.definingPoly == NullUniPolyId) return std::nullopt;

    std::vector<poly::Integer> lpCoeffs;
    lpCoeffs.reserve(coeffs.size());
    for (auto it = coeffs.rbegin(); it != coeffs.rend(); ++it) {
        lpCoeffs.emplace_back(*it);
    }
    poly::UPolynomial up(lpCoeffs);

    auto loOpt = mpqToDyadicRational(ar.lower);
    auto hiOpt = mpqToDyadicRational(ar.upper);
    if (!loOpt || !hiOpt) return std::nullopt;

    poly::DyadicInterval di(*loOpt, *hiOpt);
    return poly::AlgebraicNumber(std::move(up), di);
}
#endif

RootSet LibpolyBackend::isolateRealRootsAlgebraic(
    PolyId p, const SamplePoint& prefix, VarId mainVar) {
#ifndef XOLVER_HAS_LIBPOLY
    (void)p; (void)prefix; (void)mainVar;
    return RootSet{};
#else
    if (!libKernel_) return RootSet{};

    // Heap-corruption firewall: refuse before touching libpoly when substituting
    // `prefix` into `p` would build multi-Kbit coefficients (degree-in-v ×
    // coordinate-magnitude). Verified on mgc eq_big: libpoly's root isolation
    // corrupts the heap on such inputs. crashOccurred ⇒ callers treat as
    // inconclusive (→ Unknown). Refusing pre-call keeps libpoly's context clean.
    if (fwTrips(fwSubstitutedBits(*this, *kernel_, p, prefix),
                "isolateRealRootsAlgebraic")) {
        RootSet r; r.crashOccurred = true; return r;
    }

    const poly::Polynomial& poly = libKernel_->getPolynomial(p);
    poly::Assignment assignment(libKernel_->context());

    for (size_t i = 0; i < prefix.numVars(); ++i) {
        poly::Variable var = libKernel_->getVariable(std::string(kernel_->varName(prefix.varOrder[i])));
        const auto& val = prefix.values[i];
        if (val.isRational()) {
            assignment.set(var, poly::Value(poly::Rational(val.rational)));
        } else if (val.isAlgebraic()) {
            const auto& ar = val.root;
            const auto& coeffs = getUni(ar.definingPoly);
            auto algOpt = algebraicRootToPolyAlg(ar, coeffs);
            if (!algOpt) return RootSet{};
            assignment.set(var, poly::Value(*algOpt));
        } else {
            return RootSet{};
        }
    }

    std::vector<poly::Value> roots;
    // Install crash recovery around libpoly root isolation.
    g_oldSegvHandler = std::signal(SIGSEGV, libpolyCrashHandler);
    g_oldFpeHandler  = std::signal(SIGFPE,  libpolyCrashHandler);
    g_libpolyCrashRecoveryActive = 1;
    int jumped = sigsetjmp(g_libpolyJmpBuf, 1);
    if (jumped == 0) {
        roots = poly::isolate_real_roots(poly, assignment);
    }
    g_libpolyCrashRecoveryActive = 0;
    std::signal(SIGSEGV, g_oldSegvHandler);
    std::signal(SIGFPE,  g_oldFpeHandler);
    if (jumped != 0) {
        RootSet result;
        result.crashOccurred = true;
        return result;
    }

    RootSet result;
    result.roots.reserve(roots.size());

    for (size_t i = 0; i < roots.size(); ++i) {
        const auto& r = roots[i];
        if (poly::is_rational(r)) {
            const poly::Rational& rat = poly::as_rational(r);
            mpq_class q = *poly::detail::cast_to_gmp(&rat);
            result.roots.push_back(RealAlg::fromRational(std::move(q)));
        } else if (poly::is_algebraic_number(r)) {
            const poly::AlgebraicNumber& an = poly::as_algebraic_number(r);
            const poly::DyadicRational& lo = poly::get_lower_bound(an);
            const poly::DyadicRational& hi = poly::get_upper_bound(an);

            poly::Integer loNumInt = poly::numerator(lo);
            poly::Integer loDenInt = poly::denominator(lo);
            poly::Integer hiNumInt = poly::numerator(hi);
            poly::Integer hiDenInt = poly::denominator(hi);
            mpz_class loNum = *poly::detail::cast_to_gmp(&loNumInt);
            mpz_class loDen = *poly::detail::cast_to_gmp(&loDenInt);
            mpz_class hiNum = *poly::detail::cast_to_gmp(&hiNumInt);
            mpz_class hiDen = *poly::detail::cast_to_gmp(&hiDenInt);

            mpq_class lowerQ(loNum, loDen);
            mpq_class upperQ(hiNum, hiDen);

            // Defensive: libpoly may represent simple rationals (0, 1, -1) as
            // LP_VALUE_ALGEBRAIC with a null defining polynomial (f == nullptr).
            // In that case, treat them as rational roots.
            if (!an.get_internal()->f) {
                result.roots.push_back(RealAlg::fromRational(std::move(lowerQ)));
                continue;
            }

            // Extract defining polynomial from libpoly AlgebraicNumber
            poly::UPolynomial defPoly = poly::get_defining_polynomial(an);
            std::vector<poly::Integer> defCoeffs = poly::coefficients(defPoly);
            std::vector<mpz_class> coeffs;
            coeffs.reserve(defCoeffs.size());
            for (auto it = defCoeffs.rbegin(); it != defCoeffs.rend(); ++it) {
                coeffs.push_back(*poly::detail::cast_to_gmp(&*it));
            }
            UniPolyId upId = allocUni(std::move(coeffs));

            AlgebraicRoot ar;
            ar.definingPoly = upId;
            ar.rootIndex = static_cast<int>(i);
            ar.lower = std::move(lowerQ);
            ar.upper = std::move(upperQ);
            result.roots.push_back(RealAlg::fromAlgebraic(std::move(ar)));
        } else {
            return RootSet{};
        }
    }

    return result;
#endif
}

Sign LibpolyBackend::signAt(PolyId p, const SamplePoint& sample) {
    // Layer 0: empty sample
    if (sample.varOrder.empty()) {
        if (kernel_->isConstant(p)) {
            mpq_class c = kernel_->toConstant(p);
            if (c > 0) return Sign::Pos;
            if (c < 0) return Sign::Neg;
            return Sign::Zero;
        }
        return Sign::Unknown;
    }

    // Count algebraic values
    int algCount = 0;
    for (const auto& v : sample.values) {
        if (v.isAlgebraic()) ++algCount;
    }

    // Layer 1: all rational
    if (algCount == 0) {
        return signAtRational(p, sample);
    }

    // Layer 2: exactly one algebraic variable
    if (algCount == 1) {
        return signAtOneAlgebraic(p, sample);
    }

    // Layer 3: algebraic tower (multiple algebraic variables)
    return signAtTower(p, sample);
}

Sign LibpolyBackend::signAtRational(PolyId p, const SamplePoint& sample) {
    auto map = toRationalMap(sample);
    int s = kernel_->sgnVarId(p, map);
    // Verification: evaluate manually using terms
    auto termsOpt = kernel_->terms(p);
    if (termsOpt) {
        mpq_class manualVal(0);
        for (const auto& term : *termsOpt) {
            mpq_class coeff(term.coefficient);
            for (const auto& [varId, exp] : term.powers) {
                auto it = map.find(varId);
                if (it != map.end()) {
                    mpq_class factor(1);
                    for (int i = 0; i < exp; ++i) factor *= it->second;
                    coeff *= factor;
                } else {
                    coeff = 0; // missing variable
                    break;
                }
            }
            manualVal += coeff;
        }
        int manualSgn = (manualVal > 0) ? 1 : (manualVal < 0) ? -1 : 0;
        if (manualSgn != s) {
            std::cerr << "[VERIFY-FAIL] signAtRational: poly=" << kernel_->toString(p)
                      << " sgnVarId=" << s << " manual=" << manualSgn
                      << " manualVal=" << manualVal.get_str() << std::endl;
            for (const auto& [vid, val] : map) {
                std::cerr << "  " << kernel_->varName(vid) << "=" << val.get_str() << std::endl;
            }
        }
    }
    if (s < 0) return Sign::Neg;
    if (s > 0) return Sign::Pos;
    return Sign::Zero;
}

Sign LibpolyBackend::signAtOneAlgebraic(PolyId p, const SamplePoint& sample) {
    int algIdx = -1;
    for (size_t i = 0; i < sample.values.size(); ++i) {
        if (sample.values[i].isAlgebraic()) {
            algIdx = static_cast<int>(i);
            break;
        }
    }
    if (algIdx < 0) return Sign::Unknown;

    VarId algVar = sample.varOrder[algIdx];

    // Build rational prefix (all variables except the algebraic one)
    SamplePoint rationalPrefix;
    for (size_t i = 0; i < sample.values.size(); ++i) {
        if (static_cast<int>(i) == algIdx) continue;
        if (sample.values[i].isRational()) {
            rationalPrefix.push(sample.varOrder[i], RealAlg::fromRational(sample.values[i].rational));
        }
    }

    // Specialize polynomial to univariate in algVar
    UniPolyId g = specializeToUnivariate(p, rationalPrefix, algVar);
    if (g == NullUniPolyId) {
#ifndef NDEBUG
        std::cerr << "[CDCAC]       signAtOneAlgebraic: specializeToUnivariate failed" << std::endl;
#endif
        return Sign::Unknown;
    }

#ifndef NDEBUG
    std::cerr << "[CDCAC]       signAtOneAlgebraic: g=";
    for (auto c : getUni(g)) std::cerr << c.get_str() << " ";
    std::cerr << "alpha=[" << sample.values[algIdx].root.lower.get_str() << "," << sample.values[algIdx].root.upper.get_str() << "]"
              << " defPoly=" << sample.values[algIdx].root.definingPoly
              << " rootIdx=" << sample.values[algIdx].root.rootIndex << std::endl;
#endif

    Sign s = signUnivariateAtAlgebraic(g, sample.values[algIdx].root);
#ifndef NDEBUG
    std::cerr << "[CDCAC]       signAtOneAlgebraic: result=" << (int)s << std::endl;
#endif
    return s;
}

Sign LibpolyBackend::signAtTower(PolyId p, const SamplePoint& sample) {
    // Collect algebraic variable indices (highest level first for tower reduction)
    std::vector<size_t> algIndices;
    for (size_t i = 0; i < sample.values.size(); ++i) {
        if (sample.values[i].isAlgebraic()) {
            algIndices.push_back(i);
        }
    }
    if (algIndices.empty()) return signAtRational(p, sample);
    if (algIndices.size() == 1) return signAtOneAlgebraic(p, sample);

    // Patch 7 invariant: sample.prefix(k) = variables at levels [0, k).
    // Tower reduction processes from highest level to lowest.
    // When reducing modulo level i's defining polynomial, the prefix contains
    // all variables at levels [0, i), which were used to create the univariate
    // defining polynomial via specializeToUnivariate.
    PolyId current = p;
    Sign scaleSign = Sign::Pos;

    for (auto it = algIndices.rbegin(); it != algIndices.rend(); ++it) {
        size_t idx = *it;
        const auto& val = sample.values[idx];
        if (!val.isAlgebraic()) continue;

        const AlgebraicRoot& alpha = val.root;
        // Patch 10: missing definingPoly → Unknown (hard rule)
        if (alpha.definingPoly == NullUniPolyId) return Sign::Unknown;

        // Convert the univariate defining polynomial back to a PolyId
        VarId var = sample.varOrder[idx];
        PolyId definingPoly = univariateToPoly(getUni(alpha.definingPoly), var);
        // Patch 6 + 8: pseudo-remainder with scale tracking
        auto pr = kernel_->pseudoRemainderWithScale(current, definingPoly, var);
        if (!pr.ok()) {
#ifndef NDEBUG
            std::cerr << "[CDCAC]       signAtTower: prem failed" << std::endl;
#endif
            return Sign::Unknown;
        }
        current = pr.remainder;
        if (pr.exponent > 0 && pr.scaleFactor != NullPoly) {
            if (kernel_->isConstant(pr.scaleFactor)) {
                mpq_class c = kernel_->toConstant(pr.scaleFactor);
                if (c == 0) {
                    // Leading coefficient nullified at sample: degeneracy
                    return Sign::Unknown;
                }
                Sign s = (c > 0) ? Sign::Pos : Sign::Neg;
                if (pr.exponent % 2 != 0) {
                    scaleSign = multiplySigns(scaleSign, s);
                }
                // even exponent: sign is always positive, no change needed
            } else {
                // Non-constant scale factor in tower reduction.
                // In normal operation, definingPoly has constant coefficients,
                // so scaleFactor should always be constant.
                // If not, return Unknown conservatively.
                return Sign::Unknown;
            }
        }
    }

    // After tower reduction, verify no algebraic variables remain in current.
    // If deg(current, var) < deg(definingPoly, var), pseudo-remainder leaves
    // var in current. signAtRational would then pass an incomplete assignment
    // to libpoly, causing crashes on uninitialized algebraic variables.
    bool hasRemainingAlg = false;
    auto termsOpt = kernel_->terms(current);
    if (termsOpt) {
        for (const auto& term : *termsOpt) {
            for (const auto& [varId, exp] : term.powers) {
                for (size_t idx : algIndices) {
                    if (sample.varOrder[idx] == varId) {
                        hasRemainingAlg = true;
                        break;
                    }
                }
                if (hasRemainingAlg) break;
            }
            if (hasRemainingAlg) break;
        }
    } else {
        // Cannot inspect terms: conservatively return Unknown
        return Sign::Unknown;
    }

    if (hasRemainingAlg) {
        // Tower reduction did not eliminate all algebraic variables.
        // Use libpoly direct evaluation with algebraic assignment.
#ifndef XOLVER_HAS_LIBPOLY
        return Sign::Unknown;
#else
        if (!libKernel_) return Sign::Unknown;
        // ANTI-CORRUPTION / never-crash rule: building libpoly AlgebraicNumbers +
        // poly::sgn over an algebraic assignment can SIGSEGV deep in libpoly. The
        // sigsetjmp crash-recovery harness lives in signAtSampleGuarded (its own
        // frame) so this caller's live locals (scaleSign/current) cannot be
        // clobbered by longjmp. A recovered crash ⇒ Sign::Unknown.
        Sign s = signAtSampleGuarded(current, sample);
        if (s == Sign::Unknown) return Sign::Unknown;
        return multiplySigns(scaleSign, s);
#endif
    }

    // After tower reduction, evaluate at the (now rational-only) sample point.
    Sign s = signAtRational(current, sample);
    if (s == Sign::Unknown) return Sign::Unknown;
    return multiplySigns(scaleSign, s);
}

PolyId LibpolyBackend::univariateToPoly(const std::vector<mpz_class>& coeffs, VarId var) {
    PolyId result = kernel_->mkZero();
    int degree = static_cast<int>(coeffs.size()) - 1;
    for (int i = 0; i <= degree; ++i) {
        int power = degree - i;
        PolyId term = kernel_->mkConst(mpq_class(coeffs[i]));
        if (power > 0) {
            PolyId varPoly = kernel_->mkVar(var);
            term = kernel_->mul(term, kernel_->pow(varPoly, static_cast<uint32_t>(power)));
        }
        result = kernel_->add(result, term);
    }
    return result;
}

UniPolyId LibpolyBackend::specializeToUnivariate(PolyId p, const SamplePoint& prefix, VarId mainVar) {
#ifndef NDEBUG
    std::cerr << "[CDCAC]       specializeToUnivariate: input=" << kernel_->toString(p) << std::endl;
#endif

    // Convert p -> RationalPolynomial ONCE, substitute every rational prefix
    // value in RP space (no per-variable libpoly round-trip), then convert back
    // to a primitive-integer PolyId ONCE. This collapses the old per-cell
    // (k prefix substitutions + 1 final) = k+1 full libpoly<->RP round-trips —
    // each allocating fresh libpoly polynomials + GMP — into a single round-trip.
    // specializeToUnivariate is the lifting (solveLevel) hot path; the round-trip
    // churn was the dominant _int_malloc cost / OOM source. Verdict-preserving:
    // substitution of distinct prefix vars commutes and toPrimitiveInteger's
    // scale is positive (same roots -> same cell boundaries). The RP detour also
    // bypasses libpoly's main_variable restriction in coefficient extraction.
    auto rpOpt = RationalPolynomial::fromPolyId(p, *kernel_);
    if (!rpOpt) {
        return NullUniPolyId;
    }
    RationalPolynomial rp = std::move(*rpOpt);

    // Algebraic prefix values are not supported in P2a.
    for (size_t i = 0; i < prefix.numVars(); ++i) {
        if (!prefix.values[i].isRational()) {
            return NullUniPolyId;
        }
        rp = rp.substituteRational(prefix.varOrder[i], prefix.values[i].rational);
    }

    rp.normalize();
    auto norm = rp.toPrimitiveInteger(*kernel_);
    if (!norm.ok()) {
        return NullUniPolyId;
    }

    // Extract univariate coefficients in mainVar from the normalized polynomial
    auto termsOpt = kernel_->terms(norm.poly);
    if (!termsOpt) {
        return NullUniPolyId;
    }

    // Find maximum degree of mainVar and check for other variables
    int maxDegree = -1;
    for (const auto& term : *termsOpt) {
        int deg = 0;
        bool hasOtherVars = false;
        for (const auto& [varId, exp] : term.powers) {
            if (varId == mainVar) {
                deg = exp;
            } else {
                hasOtherVars = true;
            }
        }
        if (hasOtherVars) {
            // Contains other variables: not univariate in mainVar
            return NullUniPolyId;
        }
        maxDegree = std::max(maxDegree, deg);
    }

    if (maxDegree < 0) {
        // Constant polynomial
        mpq_class c = kernel_->toConstant(norm.poly);
        if (c.get_den() != 1) return NullUniPolyId;
        return allocUni(std::vector<mpz_class>{c.get_num()});
    }

    std::vector<mpz_class> coeffs(maxDegree + 1, mpz_class(0));
    for (const auto& term : *termsOpt) {
        int deg = 0;
        for (const auto& [varId, exp] : term.powers) {
            if (varId == mainVar) deg = exp;
        }
        coeffs[maxDegree - deg] = mpz_class(term.coefficient);
    }

    return allocUni(std::move(coeffs));
}

ProjectionResult LibpolyBackend::projectionPolys(
    const std::vector<PolyId>& polys,
    VarId eliminateVar,
    ProjectionMode mode) {
#ifndef XOLVER_HAS_LIBPOLY
    (void)polys; (void)eliminateVar; (void)mode;
    return {ProjectionStatus::BackendFailure, {}};
#else
    if (!libKernel_) {
        return {ProjectionStatus::BackendFailure, {}};
    }
    if (mode != ProjectionMode::Conservative) {
        return {ProjectionStatus::UnsupportedMode, {}};
    }

    std::string elimName(kernel_->varName(eliminateVar));
    poly::Variable elimPolyVar = libKernel_->resolvePolyVar(eliminateVar);

    std::unordered_set<std::string> seen;
    std::vector<PolyId> result;

    auto addIfNew = [&](poly::Polynomial p) {
        if (poly::is_constant(p)) return;
        PolyId id = libKernel_->alloc(std::move(p));
        std::string s = kernel_->toString(id);
        if (seen.insert(s).second) {
            result.push_back(id);
        }
    };

    for (PolyId p : polys) {
        // Skip polynomials that don't contain eliminateVar
        auto vars = kernel_->variables(p);
        if (std::find(vars.begin(), vars.end(), elimName) == vars.end()) {
            continue;
        }

        const poly::Polynomial& poly = libKernel_->getPolynomial(p);

        // Hard requirement: main_variable must be eliminateVar
        if (poly::main_variable(poly) != elimPolyVar) {
            return {ProjectionStatus::UnsupportedVarOrder, {}};
        }

        try {
            // Coefficients (including leading coefficient)
            for (size_t i = 0; i <= poly::degree(poly); ++i) {
                poly::Polynomial coeff = poly::coefficient(poly, i);
                if (!poly::is_constant(coeff)) {
                    addIfNew(std::move(coeff));
                }
            }

            // Discriminant
            poly::Polynomial disc = poly::discriminant(poly);
            if (!poly::is_constant(disc)) {
                addIfNew(std::move(disc));
            }
        } catch (...) {
            return {ProjectionStatus::BackendFailure, {}};
        }
    }

    // Pairwise resultants
    for (size_t i = 0; i < polys.size(); ++i) {
        auto vars_i = kernel_->variables(polys[i]);
        bool has_i = std::find(vars_i.begin(), vars_i.end(), elimName) != vars_i.end();
        if (!has_i) continue;

        const poly::Polynomial& pi = libKernel_->getPolynomial(polys[i]);
        if (poly::main_variable(pi) != elimPolyVar) {
            return {ProjectionStatus::UnsupportedVarOrder, {}};
        }

        for (size_t j = i + 1; j < polys.size(); ++j) {
            auto vars_j = kernel_->variables(polys[j]);
            bool has_j = std::find(vars_j.begin(), vars_j.end(), elimName) != vars_j.end();
            if (!has_j) continue;

            const poly::Polynomial& pj = libKernel_->getPolynomial(polys[j]);
            if (poly::main_variable(pj) != elimPolyVar) {
                return {ProjectionStatus::UnsupportedVarOrder, {}};
            }

            try {
                poly::Polynomial res = poly::resultant(pi, pj);
                if (!poly::is_constant(res)) {
                    addIfNew(std::move(res));
                }
            } catch (...) {
                return {ProjectionStatus::BackendFailure, {}};
            }
        }
    }

    if (result.empty()) {
        return {ProjectionStatus::EmptyBecauseNoRelevantPolys, {}};
    }
    return {ProjectionStatus::Success, std::move(result)};
#endif
}

bool LibpolyBackend::validateRootIsolation(UniPolyId p, const RootSet& roots) {
    (void)p;  // unused: refinement uses the per-root defining polynomial
    if (roots.empty()) return true;

    // Per-root sanity: algebraic intervals must have lower <= upper.
    for (const auto& r : roots.roots) {
        if (r.isAlgebraic() && r.root.lower > r.root.upper) return false;
    }

    // Check that adjacent roots are strictly ordered. libpoly's root isolation
    // can return abutting intervals (e.g. [3/4, 1] and [1, 5/4] for the roots
    // 99/100 and 101/100 of 10000x²−20000x+9999): both intervals are correct
    // but their endpoints touch. Treating that as "invalid" loses precision
    // tests. We instead try to refine each algebraic root's bracketing
    // interval until the pair is strictly disjoint, and only fail when
    // refinement bottoms out without separating them.
    auto pointOf = [](const RealAlg& r, bool lower) -> mpq_class {
        if (r.isRational()) return r.rational;
        return lower ? r.root.lower : r.root.upper;
    };
    constexpr int kMaxRefineSteps = 40;
    auto& mutRoots = const_cast<std::vector<RealAlg>&>(roots.roots);
    for (size_t i = 1; i < mutRoots.size(); ++i) {
        auto& prev = mutRoots[i - 1];
        auto& curr = mutRoots[i];
        mpq_class prevHi = pointOf(prev, /*lower=*/false);
        mpq_class currLo = pointOf(curr, /*lower=*/true);
        int steps = 0;
        while (!(prevHi < currLo) && steps < kMaxRefineSteps) {
            bool advanced = false;
            if (prev.isAlgebraic() && refineRootInterval(prev.root)) advanced = true;
            if (curr.isAlgebraic() && refineRootInterval(curr.root)) advanced = true;
            if (!advanced) break;
            prevHi = pointOf(prev, false);
            currLo = pointOf(curr, true);
            ++steps;
        }
        if (!(prevHi < currLo)) return false;
    }

    return true;
}

VanishResult LibpolyBackend::vanishesAtPrefix(PolyId p, const SamplePoint& prefix, VarId var) {
    // V2-7: nullification detection.
    // Algebraic prefix: return Unknown (not supported).
    for (const auto& val : prefix.values) {
        if (val.isAlgebraic()) {
            return VanishResult::Unknown;
        }
    }

    // Rational prefix: substitute in RationalPolynomial space (NO per-variable
    // libpoly round-trip). The old loop called kernel_->substituteRational once
    // per prefix var, each rebuilding a libpoly polynomial via toPrimitiveInteger
    // (divide-and-conquer kernel.mul → the dominant per-cell _int_malloc churn /
    // OOM source). vanishesAtPrefix is a per-cell solveLevel hot path and only
    // needs a scale-invariant zero query (contains/isZero/coefficients-all-zero),
    // so substituting in RP space (rational coeffs, normalized once) and answering
    // directly is verdict-equivalent with a single libpoly->RP conversion.
    auto rpOpt = RationalPolynomial::fromPolyId(p, *kernel_);
    if (!rpOpt) {
        return VanishResult::Unknown;
    }
    RationalPolynomial rp = std::move(*rpOpt);
    for (size_t i = 0; i < prefix.numVars(); ++i) {
        if (!prefix.values[i].isRational()) {
            return VanishResult::Unknown;
        }
        rp = rp.substituteRational(prefix.varOrder[i], prefix.values[i].rational);
    }
    rp.normalize();

    // If the polynomial doesn't contain var, it's a constant w.r.t. var.
    if (!rp.contains(var)) {
        return rp.isZero() ? VanishResult::Vanishes : VanishResult::NonVanishes;
    }

    // Still contains var: nullification requires ALL coefficients w.r.t. var zero.
    auto coeffs = rp.coefficients(var);
    for (const auto& c : coeffs) {
        if (!c.isZero()) {
            return VanishResult::NonVanishes;
        }
    }
    return VanishResult::Vanishes;
}

std::unordered_map<VarId, mpq_class> LibpolyBackend::toRationalMap(const SamplePoint& sample) const {
    std::unordered_map<VarId, mpq_class> map;
    for (size_t i = 0; i < sample.varOrder.size(); ++i) {
        if (sample.values[i].isRational()) {
            map[sample.varOrder[i]] = sample.values[i].rational;
        }
    }
    return map;
}

mpq_class LibpolyBackend::evalUniAtRational(const std::vector<mpz_class>& coeffs, const mpq_class& q) const {
    // coeffs are from high degree to constant term
    // Evaluate using Horner's method
    if (coeffs.empty()) return mpq_class(0);
    mpq_class result = coeffs[0];  // highest degree coefficient
    for (size_t i = 1; i < coeffs.size(); ++i) {
        result = result * q + coeffs[i];
    }
    return result;
}

// ------------------------------------------------------------------
// P2a univariate algebraic helpers
// ------------------------------------------------------------------

UniPolyId LibpolyBackend::gcdUni(UniPolyId a, UniPolyId b) {
#ifndef XOLVER_HAS_LIBPOLY
    (void)a; (void)b;
    return NullUniPolyId;
#else
    if (!libKernel_) return NullUniPolyId;

    const auto& ca = getUni(a);
    const auto& cb = getUni(b);

    // Convert to libpoly format (low-to-high)
    std::vector<poly::Integer> lpa, lpb;
    lpa.reserve(ca.size());
    lpb.reserve(cb.size());
    for (auto it = ca.rbegin(); it != ca.rend(); ++it) lpa.emplace_back(*it);
    for (auto it = cb.rbegin(); it != cb.rend(); ++it) lpb.emplace_back(*it);

    poly::UPolynomial upa(lpa);
    poly::UPolynomial upb(lpb);

    poly::UPolynomial g = poly::gcd(upa, upb);

    // Convert back to high-to-low
    std::vector<poly::Integer> gCoeffs = poly::coefficients(g);
    std::vector<mpz_class> result;
    result.reserve(gCoeffs.size());
    for (auto it = gCoeffs.rbegin(); it != gCoeffs.rend(); ++it) {
        result.push_back(*poly::detail::cast_to_gmp(&*it));
    }

    return allocUni(std::move(result));
#endif
}

bool LibpolyBackend::isConstantUni(UniPolyId p) const {
    const auto& c = getUni(p);
    return c.size() == 1 && c[0] != 0;
}

UniPolyId LibpolyBackend::exactDivideUni(UniPolyId a, UniPolyId b) {
    const auto& ca = getUni(a);
    const auto& cb = getUni(b);

    // Division by zero
    if (cb.empty() || (cb.size() == 1 && cb[0] == 0)) {
        return NullUniPolyId;
    }
    // Zero dividend
    if (ca.empty() || (ca.size() == 1 && ca[0] == 0)) {
        return allocUni(std::vector<mpz_class>{0});
    }

    int degA = static_cast<int>(ca.size()) - 1;
    int degB = static_cast<int>(cb.size()) - 1;

    if (degA < degB) {
        return NullUniPolyId;
    }

    // Convert to rational coefficients for exact division
    std::vector<mpq_class> dividend;
    dividend.reserve(ca.size());
    for (const auto& c : ca) dividend.emplace_back(c);

    std::vector<mpq_class> divisor;
    divisor.reserve(cb.size());
    for (const auto& c : cb) divisor.emplace_back(c);

    std::vector<mpq_class> quotient(degA - degB + 1);

    for (int i = 0; i <= degA - degB; ++i) {
        mpq_class q = dividend[i] / divisor[0];
        quotient[i] = q;
        for (int j = 0; j <= degB; ++j) {
            dividend[i + j] -= q * divisor[j];
        }
    }

    // Check remainder is zero
    for (size_t i = 0; i < dividend.size(); ++i) {
        if (dividend[i] != 0) {
            return NullUniPolyId;
        }
    }

    // Convert quotient back to integer coefficients
    std::vector<mpz_class> result;
    result.reserve(quotient.size());
    for (const auto& q : quotient) {
        if (q.get_den() != 1) {
            return NullUniPolyId; // not exact integer division
        }
        result.push_back(q.get_num());
    }

    return allocUni(std::move(result));
}

Sign LibpolyBackend::signUnivariateAtAlgebraic(UniPolyId g, const AlgebraicRoot& alpha) {
    const auto& gCoeffs = getUni(g);

    // Zero polynomial
    if (gCoeffs.empty() || (gCoeffs.size() == 1 && gCoeffs[0] == 0)) {
        return Sign::Zero;
    }

#ifndef XOLVER_HAS_LIBPOLY
    return Sign::Unknown;
#else
    if (!libKernel_) return Sign::Unknown;
    if (alpha.definingPoly == NullUniPolyId) return Sign::Unknown;

    // ANTI-CORRUPTION / never-crash rule: isolate_real_roots + poly::sgn over an
    // algebraic value go through libpoly internals that can SIGSEGV on a
    // malformed / non-squarefree defining poly. The sigsetjmp crash-recovery
    // harness lives in the helper (its own frame), so this caller's locals are
    // never clobbered by longjmp; a recovered crash ⇒ Sign::Unknown.
    return signUnivariateAtAlgebraicGuarded(gCoeffs, alpha);
#endif
}

#ifdef XOLVER_HAS_LIBPOLY
// Crash-guarded poly::sgn(current, sample) where `sample` may carry algebraic
// coordinates. SIGSEGV/SIGFPE in libpoly is recovered to Sign::Unknown. The
// sigsetjmp + volatile locals are isolated in this frame so callers' locals are
// safe from longjmp clobbering (-Wclobbered).
Sign LibpolyBackend::signAtSampleGuarded(PolyId current, const SamplePoint& sample) {
    if (!libKernel_) return Sign::Unknown;
    // Heap-corruption firewall (see note above): poly::sgn over a sample that
    // substitutes a large coordinate into a high-degree term explodes the same
    // exact-rational interval arithmetic. Refuse → Sign::Unknown (inconclusive).
    if (fwTrips(fwSubstitutedBits(*this, *kernel_, current, sample), "signAtSample"))
        return Sign::Unknown;
    volatile int s = 0;
    volatile bool ok = false;
    g_oldSegvHandler = std::signal(SIGSEGV, libpolyCrashHandler);
    g_oldFpeHandler  = std::signal(SIGFPE,  libpolyCrashHandler);
    g_libpolyCrashRecoveryActive = 1;
    int jumped = sigsetjmp(g_libpolyJmpBuf, 1);
    if (jumped == 0) {
        try {
            poly::Assignment pa(libKernel_->context());
            bool buildOk = true;
            for (size_t i = 0; i < sample.numVars(); ++i) {
                poly::Variable pv = libKernel_->getVariable(std::string(kernel_->varName(sample.varOrder[i])));
                const auto& val = sample.values[i];
                if (val.isRational()) {
                    pa.set(pv, poly::Value(poly::Rational(val.rational)));
                } else if (val.isAlgebraic()) {
                    const auto& ar = val.root;
                    const auto& coeffs = getUni(ar.definingPoly);
                    auto algOpt = algebraicRootToPolyAlg(ar, coeffs);
                    if (!algOpt) { buildOk = false; break; }
                    pa.set(pv, poly::Value(*algOpt));
                }
            }
            if (buildOk) {
                s = poly::sgn(libKernel_->getPolynomial(current), pa);
                ok = true;
            }
        } catch (...) {
            ok = false;
        }
    }
    g_libpolyCrashRecoveryActive = 0;
    std::signal(SIGSEGV, g_oldSegvHandler);
    std::signal(SIGFPE,  g_oldFpeHandler);
    if (!ok) return Sign::Unknown;
    if (s < 0) return Sign::Neg;
    if (s > 0) return Sign::Pos;
    return Sign::Zero;
}

// Crash-guarded univariate algebraic sign: sgn(g) at the alpha'th real root of
// alpha.definingPoly. SIGSEGV/SIGFPE recovered to Sign::Unknown.
Sign LibpolyBackend::signUnivariateAtAlgebraicGuarded(
    const std::vector<mpz_class>& gCoeffs, const AlgebraicRoot& alpha) {
    if (!libKernel_) return Sign::Unknown;
    if (alpha.definingPoly == NullUniPolyId) return Sign::Unknown;
    // Heap-corruption firewall: multi-Kbit g / defining-poly coefficients explode
    // libpoly's univariate isolation + sgn. Refuse → Sign::Unknown.
    if (fwTrips(std::max(fwMaxCoeffBits(gCoeffs),
                         fwMaxCoeffBits(getUni(alpha.definingPoly))),
                "signUnivariateAtAlgebraic"))
        return Sign::Unknown;
    volatile int resultSign = 0;
    volatile bool ok = false;
    g_oldSegvHandler = std::signal(SIGSEGV, libpolyCrashHandler);
    g_oldFpeHandler  = std::signal(SIGFPE,  libpolyCrashHandler);
    g_libpolyCrashRecoveryActive = 1;
    int jumped = sigsetjmp(g_libpolyJmpBuf, 1);
    if (jumped == 0) {
        try {
            // Reconstruct the algebraic number DIRECTLY from its isolating dyadic
            // interval (algebraicRootToPolyAlg) instead of re-isolating ALL roots of
            // the defining poly via Sturm and indexing by rootIndex. `alpha` already
            // carries the [lower,upper] interval that uniquely pins which root it is,
            // so the full re-isolation was pure redundant work — and it ran once per
            // sign evaluation (~10^4 times/solve on an algebraic-leaf covering search,
            // each rebuilding the same degree-2 number), which read as a hang. This
            // is the same cheap construction signAtSampleGuarded already uses.
            const auto& rc = getUni(alpha.definingPoly);
            auto algOpt = algebraicRootToPolyAlg(alpha, rc);
            if (algOpt) {
                poly::Variable var = libKernel_->getVariable("x");
                std::vector<poly::Integer> gLpCoeffs;
                gLpCoeffs.reserve(gCoeffs.size());
                for (auto it = gCoeffs.rbegin(); it != gCoeffs.rend(); ++it) {
                    gLpCoeffs.emplace_back(*it);
                }
                poly::UPolynomial gUp(gLpCoeffs);
                lp_polynomial_t* lp_poly = lp_upolynomial_to_polynomial(
                    gUp.get_internal(),
                    libKernel_->context().get_polynomial_context(),
                    var.get_internal()
                );
                poly::Polynomial gPoly(lp_poly);

                // Exact algebraic sign evaluation via libpoly.
                poly::Assignment pa(libKernel_->context());
                pa.set(var, poly::Value(*algOpt));
                resultSign = poly::sgn(gPoly, pa);
                ok = true;
            }
        } catch (...) {
            ok = false;
        }
    }
    g_libpolyCrashRecoveryActive = 0;
    std::signal(SIGSEGV, g_oldSegvHandler);
    std::signal(SIGFPE,  g_oldFpeHandler);
    if (!ok) return Sign::Unknown;  // crash recovered, bad rootIndex, or eval failed
    if (resultSign < 0) return Sign::Neg;
    if (resultSign > 0) return Sign::Pos;
    return Sign::Zero;
}
#else
Sign LibpolyBackend::signAtSampleGuarded(PolyId, const SamplePoint&) { return Sign::Unknown; }
Sign LibpolyBackend::signUnivariateAtAlgebraicGuarded(
    const std::vector<mpz_class>&, const AlgebraicRoot&) { return Sign::Unknown; }
#endif

CompareResult LibpolyBackend::compareRealAlg(const RealAlg& a, const RealAlg& b) {
    // rational-rational
    if (a.isRational() && b.isRational()) {
        if (a.rational < b.rational) return CompareResult::Less;
        if (a.rational > b.rational) return CompareResult::Greater;
        return CompareResult::Equal;
    }

    // same defining poly + same rootIndex
    if (a.isAlgebraic() && b.isAlgebraic()) {
        if (a.root.definingPoly != NullUniPolyId &&
            b.root.definingPoly != NullUniPolyId &&
            a.root.definingPoly == b.root.definingPoly &&
            a.root.rootIndex == b.root.rootIndex) {
            return CompareResult::Equal;
        }
        // Same isolating interval that is a single POINT [r,r] -> both roots are
        // exactly the rational r -> Equal.
        if (a.root.lower == a.root.upper &&
            b.root.lower == b.root.upper &&
            a.root.lower == b.root.lower) {
            return CompareResult::Equal;
        }
        // NOTE: two DISTINCT close roots from DIFFERENT defining polynomials can
        // share the same coarse (non-singleton) isolating interval (e.g.
        // √(5/2)≈1.5811 and √(81/32)≈1.5910 both isolated in [1.5,1.6]). Treating
        // "same non-singleton interval ⇒ Equal" wrongly conflated them, dropping
        // distinct roots in mergeRoots (17→9) → over-wide cells → false UNSAT
        // (meti-tarski sqrt). Equality is decided ONLY by (same poly+index, above)
        // or the exact gcd test in the algebraic-algebraic refinement path below;
        // overlapping-but-distinct roots fall through to refinement there.
        // Disjoint intervals -> can determine order
        if (a.root.upper < b.root.lower) return CompareResult::Less;
        if (b.root.upper < a.root.lower) return CompareResult::Greater;
        if (a.root.upper < b.root.lower) return CompareResult::Less;
        if (b.root.upper < a.root.lower) return CompareResult::Greater;
    }

    // disjoint intervals (algebraic-algebraic)
    if (a.isAlgebraic() && b.isAlgebraic()) {
        if (a.root.upper < b.root.lower) return CompareResult::Less;
        if (b.root.upper < a.root.lower) return CompareResult::Greater;
    }

    // rational-algebraic: q is strictly outside interval
    if (a.isRational() && b.isAlgebraic()) {
        if (a.rational < b.root.lower) return CompareResult::Less;
        if (a.rational > b.root.upper) return CompareResult::Greater;
    }

    // algebraic-rational: q is strictly outside interval
    if (a.isAlgebraic() && b.isRational()) {
        if (a.root.upper < b.rational) return CompareResult::Less;
        if (a.root.lower > b.rational) return CompareResult::Greater;
    }

    // From here: need refinement (rational inside interval, or overlapping alg-alg)
#ifndef XOLVER_HAS_LIBPOLY
    return CompareResult::Unknown;
#else
    if (!libKernel_) return CompareResult::Unknown;

    // rational-algebraic inside interval: eval defining poly at q
    if (a.isRational() && b.isAlgebraic()) {
        if (b.root.definingPoly != NullUniPolyId) {
            const auto& fCoeffs = getUni(b.root.definingPoly);
            mpq_class val = evalUniAtRational(fCoeffs, a.rational);
            if (val == 0) return CompareResult::Equal;

            // P2a-sign-fallback: when bisection refinement cannot move the bound
            // (e.g. lower bound is exactly a rational that is not the root),
            // use sign comparison to determine order.
            // For a squarefree polynomial with one root in [lower, upper],
            // if f(q) and f(lower) have the same sign, q and lower are on the
            // same side of the root, so q < root.
            mpq_class valLo = evalUniAtRational(fCoeffs, b.root.lower);
            if (valLo != 0) {
                bool sameSignAsLo = (val > 0) == (valLo > 0);
                return sameSignAsLo ? CompareResult::Less : CompareResult::Greater;
            }
        }

        // q is NOT a root of b's poly (val != 0 above) ⇒ q != α ⇒ DISTINCT, so
        // refine-until-disjoint terminates; a generous bound (not 20) separates
        // even ~2^-65-close pairs. Hit bound ⇒ sound Unknown.
        AlgebraicRoot mutableB = b.root;
        for (int iter = 0; iter < 4096; ++iter) {
            if (!refineRootInterval(mutableB)) break;
            if (a.rational < mutableB.lower) return CompareResult::Less;
            if (a.rational > mutableB.upper) return CompareResult::Greater;
        }
        return CompareResult::Unknown;
    }

    // algebraic-rational inside interval
    if (a.isAlgebraic() && b.isRational()) {
        if (a.root.definingPoly != NullUniPolyId) {
            const auto& fCoeffs = getUni(a.root.definingPoly);
            mpq_class val = evalUniAtRational(fCoeffs, b.rational);
            if (val == 0) return CompareResult::Equal;

            // P2a-sign-fallback: same reasoning as above.
            mpq_class valLo = evalUniAtRational(fCoeffs, a.root.lower);
            if (valLo != 0) {
                bool sameSignAsLo = (val > 0) == (valLo > 0);
                // same sign as lower bound => rational < root => root > rational => a > b
                return sameSignAsLo ? CompareResult::Greater : CompareResult::Less;
            }
        }

        AlgebraicRoot mutableA = a.root;
        for (int iter = 0; iter < 20; ++iter) {
            if (!refineRootInterval(mutableA)) break;
            if (b.rational < mutableA.lower) return CompareResult::Greater;
            if (b.rational > mutableA.upper) return CompareResult::Less;
        }
        return CompareResult::Unknown;
    }

    // algebraic-algebraic overlapping intervals
    if (a.isAlgebraic() && b.isAlgebraic()) {
        // same defining poly with different rootIndex
        if (a.root.definingPoly == b.root.definingPoly) {
            return a.root.rootIndex < b.root.rootIndex
                ? CompareResult::Less
                : CompareResult::Greater;
        }

        // STEP 2 — exact equality via gcd-membership. gcd COPRIME (constant) ⇒ the
        // two roots are PROVABLY DISTINCT (no common algebraic root). Otherwise
        // locate both in the gcd: same gcd-root ⇒ Equal, different ⇒ ordered.
        UniPolyId d = gcdUni(a.root.definingPoly, b.root.definingPoly);
        const bool provenDistinct = (d == NullUniPolyId) || isConstantUni(d);
        if (!provenDistinct) {
            auto locA = locateRootInPolynomial(a.root, d);
            auto locB = locateRootInPolynomial(b.root, d);
            if (locA.status == RootLocateStatus::Belongs &&
                locB.status == RootLocateStatus::Belongs) {
                if (locA.rootIndexInTarget == locB.rootIndexInTarget) {
                    return CompareResult::Equal;
                }
                return locA.rootIndexInTarget < locB.rootIndexInTarget
                    ? CompareResult::Less
                    : CompareResult::Greater;
            }
        }

        // STEP 3 — certified separation: refine the isolating intervals until
        // DISJOINT, then the order is certified by disjoint intervals. SOUND: a
        // hit bound falls through to Unknown — never a guessed order.
        //   - When distinctness is PROVEN (coprime gcd), refinement is guaranteed
        //     to terminate (the roots are a finite distance apart), so use a
        //     GENEROUS bound (refine-until-disjoint) — meti-tarski trig/exp roots
        //     can be ~2^-65 apart, well past a 64-cap. With the local sign-based
        //     refineRootInterval each step is O(1) evals, so a large bound is cheap.
        //   - When distinctness is NOT proven (non-coprime gcd whose membership
        //     test was inconclusive), the roots MIGHT be equal — equal roots never
        //     separate, so keep a TIGHT cap to avoid nontermination ⇒ sound Unknown.
        const int refineCap = provenDistinct ? 4096 : 64;
        AlgebraicRoot mutableA = a.root;
        AlgebraicRoot mutableB = b.root;
        for (int iter = 0; iter < refineCap; ++iter) {
            if (mutableA.upper < mutableB.lower) return CompareResult::Less;
            if (mutableB.upper < mutableA.lower) return CompareResult::Greater;

            bool okA = refineRootInterval(mutableA);
            bool okB = refineRootInterval(mutableB);
            if (!okA || !okB) break;
        }
        return CompareResult::Unknown;   // STEP 4 — budget exhausted: do NOT guess
    }

    return CompareResult::Unknown;
#endif
}

// ------------------------------------------------------------------
// Root interval refinement and counting
// ------------------------------------------------------------------

bool LibpolyBackend::refineRootInterval(AlgebraicRoot& alpha) {
#ifndef XOLVER_HAS_LIBPOLY
    return false;
#else
    if (!libKernel_) return false;
    if (alpha.definingPoly == NullUniPolyId) return false;

    // LOCAL root-preserving bisection of the CURRENT certified isolating interval
    // [lo,hi]. The previous implementation RE-ISOLATED all roots from scratch on
    // every call and refined libpoly's fresh bracket back down to the caller's
    // width — that lost the caller's accumulated progress, paid full isolation
    // cost per step, and (worse) risked root-matching errors on high-degree
    // polynomials, so caller loops stalled and compareRealAlg returned a spurious
    // Unknown on genuinely distinct roots ~1e-8 apart (meti-tarski trig/exp).
    //
    // Instead: split [lo,hi] at its midpoint and keep the half that still
    // contains exactly one real root of the SAME defining polynomial (root count
    // via Sturm/sign-changes). Guarantees the refinement contract: the new
    // interval is a strict sub-interval of the old, still isolating, contains the
    // SAME root, and rootIndex/definingPoly are unchanged. If the count cannot
    // certify a unique half (interval not cleanly isolating, or count
    // unsupported) ⇒ return false: the caller treats "no progress" as Unknown and
    // never guesses an order or swaps in an extraneous root (fail-closed).
    const mpq_class lo = alpha.lower;
    const mpq_class hi = alpha.upper;
    if (hi <= lo) return false;                  // already a point ⇒ cannot shrink

    const mpq_class m = (lo + hi) / 2;
    const auto& coeffs = getUni(alpha.definingPoly);
    const mpq_class vm = evalUniAtRational(coeffs, m);
    if (vm == 0) {                               // exact rational root at midpoint
        alpha.lower = m; alpha.upper = m; return true;
    }
    // FAST sign-based bisection: for a SIMPLE root in an isolating interval the
    // polynomial changes sign across the root, so the half whose endpoints differ
    // in sign is the one containing it (one evalUniAtRational per endpoint — far
    // cheaper than a Sturm count, which was timing out on degree-7 meti-tarski).
    const mpq_class vlo = evalUniAtRational(coeffs, lo);
    const mpq_class vhi = evalUniAtRational(coeffs, hi);
    if (vlo != 0 && vhi != 0) {
        const bool loNeg = vlo < 0, mNeg = vm < 0, hiNeg = vhi < 0;
        if (loNeg != mNeg && mNeg == hiNeg) { alpha.upper = m; return true; }  // sole sign change in [lo,m]
        if (loNeg == mNeg && mNeg != hiNeg) { alpha.lower = m; return true; }  // sole sign change in [m,hi]
        // else: no clean single sign change (even multiplicity / non-squarefree /
        // not sign-isolating) ⇒ fall through to the exact count-based split.
    }
    // EXACT fallback (root at an endpoint, or no clean sign bracket): root-count.
    const int leftCount  = countRealRootsInInterval(alpha.definingPoly, lo, m);
    const int rightCount = countRealRootsInInterval(alpha.definingPoly, m, hi);
    if (leftCount < 0 || rightCount < 0) return false;                  // count unsupported
    if (leftCount == 1 && rightCount == 0) { alpha.upper = m; return true; }
    if (leftCount == 0 && rightCount == 1) { alpha.lower = m; return true; }
    return false;   // 0 or >1 roots in a half ⇒ not cleanly isolating ⇒ no certified shrink
#endif
}

int LibpolyBackend::countRealRootsInInterval(UniPolyId h, const mpq_class& lo, const mpq_class& hi) {
#ifndef XOLVER_HAS_LIBPOLY
    return -1;
#else
    if (!libKernel_) return -1;

    const auto& hc = getUni(h);
    // Heap-corruption firewall (crash fix): poly::count_real_roots runs an exact
    // Sturm sequence + sign-at-rational, whose internal rational_interval_pow /
    // gmpq_mul materializes multi-megabit GMP rationals on multi-Kbit inputs and
    // corrupts the heap → SIGSEGV deep in __gmpn_gcd_1 (reproduced on the 16-var
    // Economics-Mulligan-0061e CDCAC mergeRoots→compareRealAlg path). Refuse such
    // inputs BEFORE touching libpoly — both the polynomial coefficients AND the
    // interval endpoints (count_real_roots powers the endpoints). Same guard and
    // cap as isolateRealRoots / locateRootInPolynomial. -1 is the existing
    // "inconclusive/unsupported" sentinel callers already handle (refineRootInterval,
    // locateRootInPolynomial) → CDCAC falls back, never a wrong root comparison.
    const long endpointBits = std::max(
        std::max(fwZbits(lo.get_num()), fwZbits(lo.get_den())),
        std::max(fwZbits(hi.get_num()), fwZbits(hi.get_den())));
    if (fwTrips(std::max(fwMaxCoeffBits(hc), endpointBits), "countRealRootsInInterval"))
        return -1;

    std::vector<poly::Integer> hLpCoeffs;
    for (auto it = hc.rbegin(); it != hc.rend(); ++it) {
        hLpCoeffs.emplace_back(*it);
    }
    poly::UPolynomial hUp(hLpCoeffs);

    poly::RationalInterval ri{poly::Rational(lo), poly::Rational(hi)};
    // Crash firewall (SIGSEGV backstop): even under the bit-cap, count_real_roots'
    // Sturm sign-at can fault deep in GMP (__gmpn_gcd_1) on inputs the cap doesn't
    // reject — reproduced on the 16-var Economics-Mulligan-0061e CDCAC
    // mergeRoots→compareRealAlg path. Use the same sigsetjmp harness as
    // isolateRealRoots so a fault becomes -1 (the existing inconclusive sentinel)
    // instead of killing the process. SIGSEGV = bad read (heap intact) so longjmp
    // recovery is safe; this path is NOT nested inside the isolation firewall, so
    // the single global jmp-buf is not clobbered.
    int rc = -1;
    g_oldSegvHandler = std::signal(SIGSEGV, libpolyCrashHandler);
    g_oldFpeHandler  = std::signal(SIGFPE,  libpolyCrashHandler);
    g_libpolyCrashRecoveryActive = 1;
    const int jumped = sigsetjmp(g_libpolyJmpBuf, 1);
    if (jumped == 0) {
        rc = static_cast<int>(poly::count_real_roots(hUp, ri));
    }
    g_libpolyCrashRecoveryActive = 0;
    std::signal(SIGSEGV, g_oldSegvHandler);
    std::signal(SIGFPE,  g_oldFpeHandler);
    return jumped == 0 ? rc : -1;
#endif
}

RootLocateResult LibpolyBackend::locateRootInPolynomial(const AlgebraicRoot& alpha, UniPolyId h) {
    if (isConstantUni(h)) {
        return {RootLocateStatus::NotBelongs, -1};
    }

    AlgebraicRoot mutableAlpha = alpha;

    while (true) {
        const auto& hCoeffs = getUni(h);
        mpq_class loVal = evalUniAtRational(hCoeffs, mutableAlpha.lower);
        mpq_class hiVal = evalUniAtRational(hCoeffs, mutableAlpha.upper);

        if (loVal == 0 || hiVal == 0) {
            if (!refineRootInterval(mutableAlpha)) {
                return {RootLocateStatus::Unknown, -1};
            }
            continue;
        }

        int count = countRealRootsInInterval(h, mutableAlpha.lower, mutableAlpha.upper);
        if (count < 0) {
            return {RootLocateStatus::Unknown, -1};
        }

        if (count == 0) {
            return {RootLocateStatus::NotBelongs, -1};
        }

        if (count == 1) {
            // Find which root of h overlaps with alpha's interval
            const auto& hc = getUni(h);
            // Heap-corruption firewall: refuse multi-Kbit univariate isolation.
            if (fwTrips(fwMaxCoeffBits(hc), "locateRootInPolynomial"))
                return {RootLocateStatus::Unknown, -1};
            std::vector<poly::Integer> hLpCoeffs;
            for (auto it = hc.rbegin(); it != hc.rend(); ++it) {
                hLpCoeffs.emplace_back(*it);
            }
            poly::UPolynomial hUp(hLpCoeffs);
            std::vector<poly::AlgebraicNumber> hRoots = poly::isolate_real_roots(hUp);
            for (size_t i = 0; i < hRoots.size(); ++i) {
                const auto& rLo = poly::get_lower_bound(hRoots[i]);
                const auto& rHi = poly::get_upper_bound(hRoots[i]);
                poly::Integer rLoNum = poly::numerator(rLo);
                poly::Integer rLoDen = poly::denominator(rLo);
                poly::Integer rHiNum = poly::numerator(rHi);
                poly::Integer rHiDen = poly::denominator(rHi);
                mpq_class hLo(*poly::detail::cast_to_gmp(&rLoNum), *poly::detail::cast_to_gmp(&rLoDen));
                mpq_class hHi(*poly::detail::cast_to_gmp(&rHiNum), *poly::detail::cast_to_gmp(&rHiDen));
                if (hLo <= mutableAlpha.upper && hHi >= mutableAlpha.lower) {
                    return {RootLocateStatus::Belongs, static_cast<int>(i)};
                }
            }
            return {RootLocateStatus::Unknown, -1};
        }

        // More than one root in interval: refine alpha
        if (!refineRootInterval(mutableAlpha)) {
            return {RootLocateStatus::Unknown, -1};
        }
    }
}

// ---------------------------------------------------------------------------
// SAFE algebraic-prefix root isolation via resultant Norm + exact interval
// filter. Replaces the crash-prone libpoly algebraic root isolation.
// ---------------------------------------------------------------------------
namespace {

struct QInterval { mpq_class lo, hi; };

QInterval qiMul(const QInterval& a, const QInterval& b) {
    mpq_class c1 = a.lo * b.lo, c2 = a.lo * b.hi, c3 = a.hi * b.lo, c4 = a.hi * b.hi;
    return { std::min({c1, c2, c3, c4}), std::max({c1, c2, c3, c4}) };
}
QInterval qiPow(const QInterval& a, int e) {
    QInterval r{ mpq_class(1), mpq_class(1) };
    for (int i = 0; i < e; ++i) r = qiMul(r, a);
    return r;
}

// Bisect an isolating interval [lo,hi] of `coeffs` (high-to-low) once, keeping
// the sub-interval that still brackets a sign change. No-op once it collapses.
void bisectInterval(const std::vector<mpz_class>& coeffs,
                    mpq_class& lo, mpq_class& hi,
                    const std::function<mpq_class(const std::vector<mpz_class>&, const mpq_class&)>& eval) {
    if (hi <= lo) return;
    mpq_class mid = (lo + hi) / 2;
    mpq_class fmid = eval(coeffs, mid);
    if (fmid == 0) { lo = mid; hi = mid; return; }
    mpq_class flo = eval(coeffs, lo);
    if (flo == 0) { hi = lo; return; }
    bool loPos = flo > 0, midPos = fmid > 0;
    if (loPos != midPos) hi = mid; else lo = mid;
}

} // namespace

RootSet LibpolyBackend::isolateRealRootsViaNorm(
    PolyId p, const SamplePoint& prefix, VarId mainVar, bool& supported) {

    supported = false;   // set true only once we reach the certified isolation
    RootSet empty;

    // 1. Require exactly one algebraic prefix coordinate (single extension).
    int algIdx = -1, algCount = 0;
    for (size_t i = 0; i < prefix.values.size(); ++i) {
        if (prefix.values[i].isAlgebraic()) { ++algCount; algIdx = static_cast<int>(i); }
    }
    if (algCount != 1) {                 // multi-extension / none → tower path takes over
        static const bool kTd = std::getenv("XOLVER_NRA_LAZARD_DIAG") != nullptr;
        if (kTd) std::cerr << "[LAZVAL] norm bail=algCount=" << algCount << std::endl;
        return empty;
    }
    VarId algVar = prefix.varOrder[algIdx];
    const AlgebraicRoot& alpha = prefix.values[algIdx].root;
    if (alpha.definingPoly == NullUniPolyId) return empty;

    // 2. p as RationalPolynomial; substitute the rational prefix coordinates.
    auto rpOpt = RationalPolynomial::fromPolyId(p, *kernel_);
    if (!rpOpt) return empty;
    RationalPolynomial p1 = *rpOpt;
    for (size_t i = 0; i < prefix.values.size(); ++i) {
        if (static_cast<int>(i) == algIdx) continue;
        if (prefix.values[i].isRational())
            p1 = p1.substituteRational(prefix.varOrder[i], prefix.values[i].rational);
    }
    p1.normalize();
    if (p1.isZero() || p1.isConstant()) return empty;
    for (VarId v : p1.variables()) {
        if (v != algVar && v != mainVar) return empty;   // residual var → Unknown
    }
    if (!p1.contains(mainVar)) return empty;

    // 3. m(A) as a RationalPolynomial in algVar (coeffs are high-to-low).
    RationalPolynomial mA;
    {
        const auto& mco = getUni(alpha.definingPoly);
        int deg = static_cast<int>(mco.size()) - 1;
        for (size_t i = 0; i < mco.size(); ++i) {
            int power = deg - static_cast<int>(i);
            if (mco[i] == 0) continue;
            if (power == 0) mA.addConstant(mpq_class(mco[i]));
            else mA.addVar(algVar, power, mpq_class(mco[i]));
        }
        mA.normalize();
    }
    if (mA.degree(algVar) < 1) return empty;

    // 4. N(mainVar) = Res_A(m, p1) — eliminate the algebraic coordinate.
    RationalPolynomial N = resultant(mA, p1, algVar);
    N.normalize();
    if (N.isZero() || N.isConstant()) return empty;
    for (VarId v : N.variables()) if (v != mainVar) return empty;

    // 5. Isolate N's real roots via the SAFE rational univariate path.
    UniPolyId Nuni = specializeToUnivariate(N.toPolyId(*kernel_), SamplePoint{}, mainVar);
    if (Nuni == NullUniPolyId) return empty;
    RootSet candidates = isolateRealRoots(Nuni);
    // Firewall bail ⇒ inconclusive: must NOT fall through to "0 roots certified".
    if (candidates.crashOccurred) { supported = false; return empty; }

    // 6. Exact filter: keep β with p1(a, β) = 0, decided by rational interval
    //    refinement of a's and β's isolating intervals (fully rational; cannot
    //    crash).
    const auto& aco = getUni(alpha.definingPoly);
    auto evalUni = [this](const std::vector<mpz_class>& c, const mpq_class& q) {
        return evalUniAtRational(c, q);
    };

    RootSet out;
    for (const auto& beta : candidates.roots) {
        mpq_class aLo = alpha.lower, aHi = alpha.upper;
        bool bRational = beta.isRational();
        mpq_class bLo, bHi;
        std::vector<mpz_class> bco;
        if (bRational) { bLo = bHi = beta.rational; }
        else {
            if (beta.root.definingPoly == NullUniPolyId) continue;
            bco = getUni(beta.root.definingPoly);
            bLo = beta.root.lower; bHi = beta.root.upper;
        }

        bool isRoot = true;
        for (int d = 0; d < 80; ++d) {
            QInterval V{ mpq_class(0), mpq_class(0) };
            for (const auto& [mon, coeff] : p1.terms()) {
                QInterval term{ coeff, coeff };
                for (const auto& [v, e] : mon) {
                    QInterval vi = (v == algVar) ? QInterval{aLo, aHi}
                                                 : QInterval{bLo, bHi};
                    term = qiMul(term, qiPow(vi, e));
                }
                V.lo += term.lo; V.hi += term.hi;
            }
            if (V.lo > 0 || V.hi < 0) { isRoot = false; break; }   // 0 ∉ V ⇒ not a root
            bisectInterval(aco, aLo, aHi, evalUni);
            if (!bRational) bisectInterval(bco, bLo, bHi, evalUni);
            if (aHi <= aLo && (bRational || bHi <= bLo)) break;
        }
        if (isRoot) out.roots.push_back(beta);
    }
    supported = true;   // certified isolation completed (0 roots is a valid answer)
    return out;
}

RootSet LibpolyBackend::isolateRealRootsViaTower(
    PolyId p, const SamplePoint& prefix, VarId mainVar, bool& supported) {

    supported = false;
    RootSet empty;
    static const bool kDiagEntry = std::getenv("XOLVER_NRA_LAZARD_DIAG") != nullptr;
    if (kDiagEntry) std::cerr << "[LAZVAL] isolateRealRootsViaTower entry" << std::endl;
    auto TD = [&](const char* why) -> RootSet {
        if (kDiagEntry) std::cerr << "[LAZVAL] tower bail=" << why << std::endl;
        return empty;
    };

    // 1. Build the field tower from the ALGEBRAIC prefix coordinates (rational
    //    coordinates are substituted into p). Each algebraic coordinate becomes
    //    a tower generator in its OWN prefix variable, with its defining poly as
    //    a MONIC minimal poly (TowerKernel requires monic). Soundness does NOT
    //    require the m_i to be irreducible (see RootMembershipOracle.h).
    auto rpOpt = RationalPolynomial::fromPolyId(p, *kernel_);
    if (!rpOpt) return TD("fromPolyId");
    RationalPolynomial p1 = *rpOpt;

    TowerContext ctx;
    int algCount = 0;
    for (size_t i = 0; i < prefix.values.size(); ++i) {
        const RealAlg& val = prefix.values[i];
        VarId v = prefix.varOrder[i];
        if (val.isRational()) { p1 = p1.substituteRational(v, val.rational); continue; }
        ++algCount;
        if (val.root.definingPoly == NullUniPolyId) return TD("null-defining-poly");
        const auto& mco = getUni(val.root.definingPoly);   // high-to-low integer coeffs
        int deg = static_cast<int>(mco.size()) - 1;
        if (deg < 1 || mco[0] == 0) return TD("bad-minpoly-degree");
        mpq_class lead(mco[0]);
        RationalPolynomial mi;
        for (size_t j = 0; j < mco.size(); ++j) {
            int power = deg - static_cast<int>(j);
            if (mco[j] == 0) continue;
            mpq_class c = mpq_class(mco[j]) / lead;        // monic-normalize
            if (power == 0) mi.addConstant(c);
            else mi.addVar(v, power, c);
        }
        mi.normalize();
        ctx.extensionVars.push_back(v);
        ctx.minimalPolys.push_back(std::move(mi));
        ctx.generators.push_back(val);
    }
    if (algCount < 1) return TD("algCount<1");             // no tower => not our case

    p1.normalize();
    if (p1.isZero() || p1.isConstant() || !p1.contains(mainVar)) return TD("p1-zero-const-or-no-mainVar");
    {
        std::set<VarId> ext(ctx.extensionVars.begin(), ctx.extensionVars.end());
        for (VarId v : p1.variables())
            if (v != mainVar && !ext.count(v)) return TD("p1-stray-var");   // residual var => Unknown
    }

    // Tower-aware real-root isolation of a polynomial F (in mainVar + tower
    // extension variables) against the tower `ctx`: Norm candidates over Q,
    // then the exact membership filter. `ok` is set false on any incomplete /
    // unsupported / inconclusive step (caller => Unknown, never UNSAT); when ok
    // is true the returned set is the certified real roots (possibly empty).
    auto isolateInTower = [this, &ctx, mainVar](const RationalPolynomial& F,
                                                bool& ok) -> RootSet {
        ok = false;
        RootSet none;
        auto nrF = towerNorm(F, mainVar, ctx);
        if (!nrF.ok) return none;                          // degenerate Norm => Unknown
        if (nrF.norm.isConstant()) { ok = true; return none; }  // no candidate roots
        UniPolyId Nu = specializeToUnivariate(nrF.norm.toPolyId(*kernel_), SamplePoint{}, mainVar);
        if (Nu == NullUniPolyId) return none;
        RootSet cands = isolateRealRoots(Nu);
        if (cands.crashOccurred) return none;   // firewall bail ⇒ ok stays false ⇒ Unknown
        RootSet kept;
        for (const auto& beta : cands.roots) {
            mpq_class lo, hi;
            if (beta.isRational()) { lo = hi = beta.rational; }
            else { lo = beta.root.lower; hi = beta.root.upper; }
            RootMembership mm = lazardRootMembership(F, mainVar, nrF.norm, lo, hi, ctx);
            if (mm == RootMembership::Keep || mm == RootMembership::Unknown) {
                kept.roots.push_back(beta);   // real boundary, or conservative over-refinement
            }
            // Drop => provably a conjugate/extraneous root here, omit (sound: not a boundary)
        }
        ok = true;
        return kept;
    };

    // 2. Norm over Q eliminates the generators; isolate its roots via the SAFE
    //    rational univariate path (never libpoly's crash-prone algebraic path).
    static const bool kDiag = std::getenv("XOLVER_NRA_LAZARD_DIAG") != nullptr;
    auto nr = towerNorm(p1, mainVar, ctx);
    if (!nr.ok) {
        if (kDiag) std::cerr << "[LAZVAL] towerNorm(p1) not ok => Unknown" << std::endl;
        return TD("towerNorm-not-ok");
    }
    if (nr.norm.isConstant()) {
        // Nullification case: the Norm degenerated to a constant. Either p1
        // genuinely has no boundary OR it nullified modulo the tower (vanishes
        // identically), in which case the Collins-style Norm path MISSES the
        // boundary the Lazard residual (lowest nonvanishing derivative) exposes.
        // Recover it via the [H3] valuation engine, then isolate the residual's
        // real roots with the SAME tower-aware machinery. Sound: any incomplete
        // / unsupported / inconclusive step => supported stays false => Unknown.
        if (kDiag) std::cerr << "[LAZVAL] Norm(p1) constant => valuation recovery" << std::endl;
        LazardValuationResult val = lazardEvaluateToUnivariate(p1, mainVar, ctx);
        if (val.status == ValuationStatus::AllDerivativesZero) {
            // [H3] lists ValuationAllDerivativesZero as an INCOMPLETE reason. While
            // it usually means p1 is identically zero in the tower (no boundary),
            // distinguishing that from a valuation limitation is not certified
            // here. For the UNSAT-critical gate (T3) we treat it conservatively as
            // unsupported => caller drops unsatTrustworthy_ => Unknown (never a
            // false UNSAT). (Relax to a certified no-boundary skip only with a
            // proof that p1 in <m_0..m_{k-1}>.)
            if (kDiag) std::cerr << "[LAZVAL] AllDerivativesZero => unsupported (conservative)" << std::endl;
            supported = false;
            return TD("AllDerivativesZero");
        }
        // status == Complete: residual is in mainVar + reduced tower coeffs.
        RationalPolynomial residual = std::move(val.univariate);
        residual.normalize();
        if (kDiag) std::cerr << "[LAZVAL] residual deg(mainVar)=" << residual.degree(mainVar)
                             << " isConst=" << residual.isConstant()
                             << " containsMain=" << residual.contains(mainVar) << std::endl;
        if (residual.isZero() || residual.isConstant() || !residual.contains(mainVar)) {
            // Residual has no boundary in mainVar (constant after reduction).
            supported = true;
            return empty;
        }
        {
            std::set<VarId> ext(ctx.extensionVars.begin(), ctx.extensionVars.end());
            for (VarId v : residual.variables())
                if (v != mainVar && !ext.count(v)) {
                    if (kDiag) std::cerr << "[LAZVAL] residual has stray var => Unknown" << std::endl;
                    return TD("residual-stray-var");   // residual var => Unknown
                }
        }
        bool ok = false;
        RootSet recovered = isolateInTower(residual, ok);
        if (kDiag) std::cerr << "[LAZVAL] residual isolate ok=" << ok
                             << " roots=" << recovered.numRoots() << std::endl;
        if (!ok) return TD("isolateInTower-residual-not-ok");   // unsupported => Unknown
        supported = true;
        return recovered;
    }

    UniPolyId Nuni = specializeToUnivariate(nr.norm.toPolyId(*kernel_), SamplePoint{}, mainVar);
    if (Nuni == NullUniPolyId) return empty;
    RootSet candidates = isolateRealRoots(Nuni);
    if (candidates.crashOccurred) return TD("isolate-firewall");   // ⇒ Unknown

    // 3. The Norm's real roots are a SOUND SUPERSET of p1's real boundaries at our
    //    embedding: every real root β of p1's specialization q(mainVar) satisfies
    //    N(β)=∏_σ p1^σ(β)=0, so β ∈ candidates. We then classify each candidate
    //    with the exact three-state oracle:
    //      - Keep    : provably a root of p1 here → a real boundary, include.
    //      - Drop    : provably NOT a root here (a conjugate's root) → spurious, omit.
    //      - Unknown : oracle can't decide → INCLUDE conservatively. Including an
    //                  extra boundary only REFINES the covering (splits one sign-
    //                  invariant region into two equally sign-invariant pieces); it
    //                  can never merge regions of different sign, so the cell stays
    //                  truth-invariant and UNSAT stays sound. This replaces the old
    //                  bail-on-Unknown, which sacrificed completeness (CONVOI2-class
    //                  multi-extension leaves) for no soundness gain.
    //    Net: never miss a real boundary (superset), never bail (complete), never
    //    merge sign regions (sound).
    RootSet out;
    for (const auto& beta : candidates.roots) {
        mpq_class lo, hi;
        if (beta.isRational()) { lo = hi = beta.rational; }
        else { lo = beta.root.lower; hi = beta.root.upper; }
        RootMembership m = lazardRootMembership(p1, mainVar, nr.norm, lo, hi, ctx);
        if (m == RootMembership::Keep || m == RootMembership::Unknown) {
            out.roots.push_back(beta);   // real boundary, or conservative over-refinement
        }
        // Drop => provably a conjugate/extraneous root here, omit (sound: not a boundary)
    }
    supported = true;
    return out;
}

} // namespace xolver
