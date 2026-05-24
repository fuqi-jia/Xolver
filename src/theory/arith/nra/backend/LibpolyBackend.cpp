#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/preprocess/SquarefreeEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/LibPolyKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"

#include <iostream>
#include <map>
#include <unordered_set>
#include <csignal>
#include <csetjmp>

#ifdef NLCOLVER_HAS_LIBPOLY
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

namespace nlcolver {

LibpolyBackend::LibpolyBackend(PolynomialKernel* kernel)
    : kernel_(kernel) {
#ifdef NLCOLVER_HAS_LIBPOLY
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

RootSet LibpolyBackend::isolateRealRoots(UniPolyId p) {
#ifndef NLCOLVER_HAS_LIBPOLY
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

#ifdef NLCOLVER_HAS_LIBPOLY
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
#ifndef NLCOLVER_HAS_LIBPOLY
    (void)p; (void)prefix; (void)mainVar;
    return RootSet{};
#else
    if (!libKernel_) return RootSet{};

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
#ifndef NLCOLVER_HAS_LIBPOLY
        return Sign::Unknown;
#else
        if (!libKernel_) return Sign::Unknown;
        try {
            poly::Assignment pa(libKernel_->context());
            for (size_t i = 0; i < sample.numVars(); ++i) {
                poly::Variable pv = libKernel_->getVariable(std::string(kernel_->varName(sample.varOrder[i])));
                const auto& val = sample.values[i];
                if (val.isRational()) {
                    pa.set(pv, poly::Value(poly::Rational(val.rational)));
                } else if (val.isAlgebraic()) {
                    const auto& ar = val.root;
                    const auto& coeffs = getUni(ar.definingPoly);
                    auto algOpt = algebraicRootToPolyAlg(ar, coeffs);
                    if (!algOpt) return Sign::Unknown;
                    pa.set(pv, poly::Value(*algOpt));
                }
            }
            int s = poly::sgn(libKernel_->getPolynomial(current), pa);
            if (s < 0) return multiplySigns(scaleSign, Sign::Neg);
            if (s > 0) return multiplySigns(scaleSign, Sign::Pos);
            return multiplySigns(scaleSign, Sign::Zero);
        } catch (...) {
            return Sign::Unknown;
        }
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
    PolyId current = p;
#ifndef NDEBUG
    std::cerr << "[CDCAC]       specializeToUnivariate: input=" << kernel_->toString(p) << std::endl;
#endif

    // Apply rational prefix substitutions one variable at a time.
    // Algebraic prefix values are not supported in P2a.
    for (size_t i = 0; i < prefix.numVars(); ++i) {
        if (!prefix.values[i].isRational()) {
#ifndef NDEBUG
            std::cerr << "[CDCAC]       specializeToUnivariate: algebraic prefix, fail" << std::endl;
#endif
            return NullUniPolyId;
        }
        VarId vid = prefix.varOrder[i];
        auto nextOpt = kernel_->substituteRational(current, vid, prefix.values[i].rational);
        if (!nextOpt) {
            return NullUniPolyId;
        }
        current = *nextOpt;
#ifndef NDEBUG
        std::cerr << "[CDCAC]       specializeToUnivariate: after sub " << kernel_->varName(vid) << "=" << prefix.values[i].rational.get_str() << " -> " << kernel_->toString(current) << std::endl;
#endif
    }

    // Convert to RationalPolynomial to handle any variable order and rational coefficients.
    // This bypasses the libpoly main_variable restriction in getIntegerCoefficients().
    auto rpOpt = RationalPolynomial::fromPolyId(current, *kernel_);
    if (!rpOpt) {
        std::cerr << "[CDCAC]       specializeToUnivariate: fromPolyId failed" << std::endl;
        return NullUniPolyId;
    }

    rpOpt->normalize();
    auto norm = rpOpt->toPrimitiveInteger(*kernel_);
    if (!norm.ok()) {
        std::cerr << "[CDCAC]       specializeToUnivariate: toPrimitiveInteger failed" << std::endl;
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
#ifndef NLCOLVER_HAS_LIBPOLY
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
    if (roots.empty()) return true;

    // Check that roots are ordered (disjoint)
    for (size_t i = 1; i < roots.roots.size(); ++i) {
        const auto& prev = roots.roots[i - 1];
        const auto& curr = roots.roots[i];
        mpq_class prevVal = prev.isRational() ? prev.rational : prev.root.upper;
        mpq_class currVal = curr.isRational() ? curr.rational : curr.root.lower;
        if (!(prevVal < currVal)) return false;
    }

    // For algebraic roots, validate interval bounds are consistent.
    // Rational roots are canonicalized (single-point), always valid.
    for (const auto& r : roots.roots) {
        if (r.isAlgebraic()) {
            if (r.root.lower > r.root.upper) return false;
        }
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

    // Rational prefix: substitute and check if zero.
    PolyId current = p;
    for (size_t i = 0; i < prefix.numVars(); ++i) {
        if (!prefix.values[i].isRational()) {
            return VanishResult::Unknown;
        }
        auto nextOpt = kernel_->substituteRational(current, prefix.varOrder[i], prefix.values[i].rational);
        if (!nextOpt) {
            return VanishResult::Unknown;
        }
        current = *nextOpt;
    }

    // After substitution, check if the remaining polynomial contains 'var'
    // and if its coefficients are all zero.
    auto rpOpt = RationalPolynomial::fromPolyId(current, *kernel_);
    if (!rpOpt) {
        return VanishResult::Unknown;
    }

    // If the polynomial doesn't contain var, it's a constant w.r.t. var.
    // Check if it's zero.
    if (!rpOpt->contains(var)) {
        return rpOpt->isZero() ? VanishResult::Vanishes : VanishResult::NonVanishes;
    }

    // The polynomial still contains var. For nullification detection,
    // we need to check if ALL coefficients w.r.t. var are zero.
    auto coeffs = rpOpt->coefficients(var);
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
#ifndef NLCOLVER_HAS_LIBPOLY
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

#ifndef NLCOLVER_HAS_LIBPOLY
    return Sign::Unknown;
#else
    if (!libKernel_) return Sign::Unknown;
    if (alpha.definingPoly == NullUniPolyId) return Sign::Unknown;

    // Reconstruct the algebraic number from root definition
    const auto& rc = getUni(alpha.definingPoly);
    std::vector<poly::Integer> rootLpCoeffs;
    rootLpCoeffs.reserve(rc.size());
    for (auto it = rc.rbegin(); it != rc.rend(); ++it) {
        rootLpCoeffs.emplace_back(*it);
    }
    poly::UPolynomial rootUp(rootLpCoeffs);
    std::vector<poly::AlgebraicNumber> roots = poly::isolate_real_roots(rootUp);
    if (alpha.rootIndex < 0 || alpha.rootIndex >= static_cast<int>(roots.size())) {
        return Sign::Unknown;
    }

    // Build gPoly once
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

    // Exact algebraic sign evaluation via libpoly
    poly::Assignment pa(libKernel_->context());
    pa.set(var, poly::Value(roots[alpha.rootIndex]));
    int s = poly::sgn(gPoly, pa);
    if (s < 0) return Sign::Neg;
    if (s > 0) return Sign::Pos;
    return Sign::Zero;
#endif
}

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
        // Same isolating interval (exact match) -> Equal
        if (a.root.lower == a.root.upper &&
            b.root.lower == b.root.upper &&
            a.root.lower == b.root.lower) {
            return CompareResult::Equal;
        }
        // Same non-singleton interval -> Equal (same root, different provenance)
        if (a.root.lower == b.root.lower && a.root.upper == b.root.upper) {
            return CompareResult::Equal;
        }
        // Disjoint intervals -> can determine order
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
#ifndef NLCOLVER_HAS_LIBPOLY
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

        AlgebraicRoot mutableB = b.root;
        for (int iter = 0; iter < 20; ++iter) {
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

        // Try gcd-based equality: locate both roots in gcd
        UniPolyId d = gcdUni(a.root.definingPoly, b.root.definingPoly);
        if (d != NullUniPolyId && !isConstantUni(d)) {
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

        // Refine until intervals separate
        AlgebraicRoot mutableA = a.root;
        AlgebraicRoot mutableB = b.root;
        for (int iter = 0; iter < 20; ++iter) {
            if (mutableA.upper < mutableB.lower) return CompareResult::Less;
            if (mutableB.upper < mutableA.lower) return CompareResult::Greater;

            bool okA = refineRootInterval(mutableA);
            bool okB = refineRootInterval(mutableB);
            if (!okA || !okB) break;
        }
        return CompareResult::Unknown;
    }

    return CompareResult::Unknown;
#endif
}

// ------------------------------------------------------------------
// Root interval refinement and counting
// ------------------------------------------------------------------

bool LibpolyBackend::refineRootInterval(AlgebraicRoot& alpha) {
#ifndef NLCOLVER_HAS_LIBPOLY
    return false;
#else
    if (!libKernel_) return false;
    if (alpha.definingPoly == NullUniPolyId) return false;

    const auto& rc = getUni(alpha.definingPoly);
    std::vector<poly::Integer> rootLpCoeffs;
    for (auto it = rc.rbegin(); it != rc.rend(); ++it) {
        rootLpCoeffs.emplace_back(*it);
    }
    poly::UPolynomial rootUp(rootLpCoeffs);
    std::vector<poly::AlgebraicNumber> roots = poly::isolate_real_roots(rootUp);
    if (alpha.rootIndex < 0 || alpha.rootIndex >= static_cast<int>(roots.size())) {
        return false;
    }

    poly::refine(roots[alpha.rootIndex]);

    const auto& newLo = poly::get_lower_bound(roots[alpha.rootIndex]);
    const auto& newHi = poly::get_upper_bound(roots[alpha.rootIndex]);

    poly::Integer loNumInt = poly::numerator(newLo);
    poly::Integer loDenInt = poly::denominator(newLo);
    poly::Integer hiNumInt = poly::numerator(newHi);
    poly::Integer hiDenInt = poly::denominator(newHi);

    mpz_class loNum = *poly::detail::cast_to_gmp(&loNumInt);
    mpz_class loDen = *poly::detail::cast_to_gmp(&loDenInt);
    mpz_class hiNum = *poly::detail::cast_to_gmp(&hiNumInt);
    mpz_class hiDen = *poly::detail::cast_to_gmp(&hiDenInt);

    alpha.lower = mpq_class(loNum, loDen);
    alpha.upper = mpq_class(hiNum, hiDen);
    return true;
#endif
}

int LibpolyBackend::countRealRootsInInterval(UniPolyId h, const mpq_class& lo, const mpq_class& hi) {
#ifndef NLCOLVER_HAS_LIBPOLY
    return -1;
#else
    if (!libKernel_) return -1;

    const auto& hc = getUni(h);
    std::vector<poly::Integer> hLpCoeffs;
    for (auto it = hc.rbegin(); it != hc.rend(); ++it) {
        hLpCoeffs.emplace_back(*it);
    }
    poly::UPolynomial hUp(hLpCoeffs);

    poly::RationalInterval ri{poly::Rational(lo), poly::Rational(hi)};
    return static_cast<int>(poly::count_real_roots(hUp, ri));
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

} // namespace nlcolver
