#include "theory/arith/nra/LibpolyBackend.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/LibPolyKernel.h"

#include <iostream>
#include <map>

#ifdef ZOLVER_HAS_LIBPOLY
#include <polyxx.h>
#endif

namespace zolver {

LibpolyBackend::LibpolyBackend(PolynomialKernel* kernel)
    : kernel_(kernel) {
#ifdef ZOLVER_HAS_LIBPOLY
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
#ifndef ZOLVER_HAS_LIBPOLY
    (void)p;
    return RootSet{};
#else
    if (!libKernel_) return RootSet{};

    const auto& coeffs = getUni(p);
    if (coeffs.empty()) return RootSet{};

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
        ar.definingPoly = p;
        ar.rootIndex = static_cast<int>(i);
        ar.lower = lowerQ;
        ar.upper = upperQ;

        result.roots.push_back(RealAlg::fromAlgebraic(std::move(ar)));
    }

    return result;
#endif
}

#ifdef ZOLVER_HAS_LIBPOLY
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

static std::vector<mpz_class> upolynomialToCoeffs(const poly::UPolynomial& up) {
    std::vector<poly::Integer> lpCoeffs = poly::coefficients(up);
    std::vector<mpz_class> result;
    result.reserve(lpCoeffs.size());
    for (const auto& c : lpCoeffs) {
        result.push_back(*poly::detail::cast_to_gmp(&c));
    }
    std::reverse(result.begin(), result.end());
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
    PolyId p, const SamplePoint& prefix, const std::string& mainVar) {
#ifndef ZOLVER_HAS_LIBPOLY
    (void)p; (void)prefix; (void)mainVar;
    return RootSet{};
#else
    if (!libKernel_) return RootSet{};

    const poly::Polynomial& poly = libKernel_->getPolynomial(p);
    poly::Assignment assignment(libKernel_->context());

    for (size_t i = 0; i < prefix.numVars(); ++i) {
        poly::Variable var = libKernel_->getVariable(prefix.varOrder[i]);
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
    try {
        roots = poly::isolate_real_roots(poly, assignment);
    } catch (...) {
        return RootSet{};
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

            AlgebraicRoot ar;
            ar.definingPoly = NullUniPolyId;
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
    int s = kernel_->sgn(p, map);
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

    const std::string& algVar = sample.varOrder[algIdx];

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
        return Sign::Unknown;
    }

    return signUnivariateAtAlgebraic(g, sample.values[algIdx].root);
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

    // Reduce modulo each defining polynomial, from highest level to lowest.
    PolyId current = p;
    for (auto it = algIndices.rbegin(); it != algIndices.rend(); ++it) {
        size_t idx = *it;
        const auto& val = sample.values[idx];
        if (!val.isAlgebraic()) continue;

        const AlgebraicRoot& alpha = val.root;
        if (alpha.definingPoly == NullUniPolyId) return Sign::Unknown;

        // Convert the univariate defining polynomial back to a PolyId
        VarId var = kernel_->getOrCreateVar(sample.varOrder[idx]);
        PolyId definingPoly = univariateToPoly(getUni(alpha.definingPoly), var);

        // Reduce current polynomial modulo the defining polynomial
        auto remOpt = kernel_->pseudoRemainder(current, definingPoly);
        if (!remOpt) {
            // pseudoRemainder may fail if main variables differ or division is unsupported.
            // Fall back to Unknown for safety.
            return Sign::Unknown;
        }
        current = *remOpt;
    }

    // After tower reduction, evaluate at the (now rational-only) sample point.
    return signAtRational(current, sample);
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

UniPolyId LibpolyBackend::specializeToUnivariate(PolyId p, const SamplePoint& prefix, const std::string& mainVar) {
    PolyId current = p;

    // Apply rational prefix substitutions one variable at a time.
    // Algebraic prefix values are not supported in P2a.
    for (size_t i = 0; i < prefix.numVars(); ++i) {
        if (!prefix.values[i].isRational()) {
            return NullUniPolyId;
        }
        VarId vid = kernel_->getOrCreateVar(prefix.varOrder[i]);
        auto nextOpt = kernel_->substituteRational(current, vid, prefix.values[i].rational);
        if (!nextOpt) return NullUniPolyId;
        current = *nextOpt;
    }

    // After substitution, extract univariate coefficients in mainVar.
    auto coeffsOpt = kernel_->getIntegerCoefficients(current, mainVar);
    if (!coeffsOpt) return NullUniPolyId;
    return allocUni(std::move(*coeffsOpt));
}

std::vector<PolyId> LibpolyBackend::projectionPolys(
    const std::vector<PolyId>& /*polys*/,
    const std::string& /*eliminateVar*/,
    ProjectionMode /*mode*/) {
    // P0: stub. P2b: implement.
    return {};
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

bool LibpolyBackend::vanishesAtPrefix(PolyId /*p*/, const SamplePoint& /*prefix*/, const std::string& /*var*/) {
    // P0: stub. P4: implement.
    return false;
}

std::unordered_map<std::string, mpq_class> LibpolyBackend::toRationalMap(const SamplePoint& sample) const {
    std::unordered_map<std::string, mpq_class> map;
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
#ifndef ZOLVER_HAS_LIBPOLY
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

bool LibpolyBackend::rootBelongsTo(const AlgebraicRoot& alpha, UniPolyId g) {
    UniPolyId d = gcdUni(alpha.definingPoly, g);
    if (d == NullUniPolyId) return false;
    if (isConstantUni(d)) return false;

    // d is a non-constant common divisor of f and g.
    // Since alpha's isolating interval contains exactly one root of f,
    // and d | f, any root of d in the interval must be alpha.
    const auto& dCoeffs = getUni(d);
    mpq_class loVal = evalUniAtRational(dCoeffs, alpha.lower);
    mpq_class hiVal = evalUniAtRational(dCoeffs, alpha.upper);

    int loSgn = (loVal > 0) ? 1 : (loVal < 0) ? -1 : 0;
    int hiSgn = (hiVal > 0) ? 1 : (hiVal < 0) ? -1 : 0;

    if (loSgn == 0 || hiSgn == 0) {
        // Endpoint is zero - unusual for isolating intervals.
        // Conservatively assume the root belongs.
        return true;
    }

    return loSgn != hiSgn;
}

Sign LibpolyBackend::signUnivariateAtAlgebraic(UniPolyId g, const AlgebraicRoot& alpha) {
    const auto& gCoeffs = getUni(g);

    // Zero polynomial
    if (gCoeffs.empty() || (gCoeffs.size() == 1 && gCoeffs[0] == 0)) {
        return Sign::Zero;
    }

    // GCD zero detection
    if (alpha.definingPoly != NullUniPolyId) {
        if (rootBelongsTo(alpha, g)) {
            return Sign::Zero;
        }
    }

    // Interval sign evaluation
    mpq_class loVal = evalUniAtRational(gCoeffs, alpha.lower);
    mpq_class hiVal = evalUniAtRational(gCoeffs, alpha.upper);

    int loSgn = (loVal > 0) ? 1 : (loVal < 0) ? -1 : 0;
    int hiSgn = (hiVal > 0) ? 1 : (hiVal < 0) ? -1 : 0;

    // Same non-zero sign at both endpoints
    if (loSgn == hiSgn && loSgn != 0) {
        return (loSgn > 0) ? Sign::Pos : Sign::Neg;
    }

#ifndef ZOLVER_HAS_LIBPOLY
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

    // Endpoint exactly zero: evaluate directly at the algebraic number
    if (loSgn == 0 || hiSgn == 0) {
        poly::Assignment pa(libKernel_->context());
        poly::Variable var = libKernel_->getVariable("x");
        pa.set(var, poly::Value(roots[alpha.rootIndex]));

        std::vector<poly::Integer> gLpCoeffs;
        gLpCoeffs.reserve(gCoeffs.size());
        for (auto it = gCoeffs.rbegin(); it != gCoeffs.rend(); ++it) {
            gLpCoeffs.emplace_back(*it);
        }
        poly::UPolynomial gUp(gLpCoeffs);

        // Convert UPolynomial to Polynomial using C API
        lp_polynomial_t* lp_poly = lp_upolynomial_to_polynomial(
            gUp.get_internal(),
            libKernel_->context().get_polynomial_context(),
            var.get_internal()
        );
        poly::Polynomial gPoly(lp_poly);

        poly::Value v = poly::evaluate(gPoly, pa);
        if (poly::is_integer(v)) {
            const poly::Integer& i = poly::as_integer(v);
            mpz_class val = *poly::detail::cast_to_gmp(&i);
            if (val > 0) return Sign::Pos;
            if (val < 0) return Sign::Neg;
            return Sign::Zero;
        }
        if (poly::is_rational(v)) {
            const poly::Rational& r = poly::as_rational(v);
            mpq_class val = *poly::detail::cast_to_gmp(&r);
            if (val > 0) return Sign::Pos;
            if (val < 0) return Sign::Neg;
            return Sign::Zero;
        }
        if (poly::is_algebraic_number(v)) {
            const poly::AlgebraicNumber& an = poly::as_algebraic_number(v);
            int s = poly::sgn(an);
            if (s < 0) return Sign::Neg;
            if (s > 0) return Sign::Pos;
            return Sign::Zero;
        }
        return Sign::Unknown;
    }

    // Signs differ: refine and retry
    for (int refineIter = 0; refineIter < 20; ++refineIter) {
        poly::refine(roots[alpha.rootIndex]);
        const poly::DyadicRational& newLo = poly::get_lower_bound(roots[alpha.rootIndex]);
        const poly::DyadicRational& newHi = poly::get_upper_bound(roots[alpha.rootIndex]);

        poly::Integer loNumInt = poly::numerator(newLo);
        poly::Integer loDenInt = poly::denominator(newLo);
        poly::Integer hiNumInt = poly::numerator(newHi);
        poly::Integer hiDenInt = poly::denominator(newHi);
        mpz_class loNum = *poly::detail::cast_to_gmp(&loNumInt);
        mpz_class loDen = *poly::detail::cast_to_gmp(&loDenInt);
        mpz_class hiNum = *poly::detail::cast_to_gmp(&hiNumInt);
        mpz_class hiDen = *poly::detail::cast_to_gmp(&hiDenInt);

        mpq_class newLoQ(loNum, loDen);
        mpq_class newHiQ(hiNum, hiDen);

        loVal = evalUniAtRational(gCoeffs, newLoQ);
        hiVal = evalUniAtRational(gCoeffs, newHiQ);

        loSgn = (loVal > 0) ? 1 : (loVal < 0) ? -1 : 0;
        hiSgn = (hiVal > 0) ? 1 : (hiVal < 0) ? -1 : 0;

        if (loSgn == hiSgn && loSgn != 0) {
            return (loSgn > 0) ? Sign::Pos : Sign::Neg;
        }
    }

    return Sign::Unknown;
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
        if (a.root.definingPoly == b.root.definingPoly &&
            a.root.rootIndex == b.root.rootIndex) {
            return CompareResult::Equal;
        }
        // Singleton rational intervals (already canonicalized, but defensive)
        if (a.root.lower == a.root.upper &&
            b.root.lower == b.root.upper &&
            a.root.lower == b.root.lower) {
            return CompareResult::Equal;
        }
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
#ifndef ZOLVER_HAS_LIBPOLY
    return CompareResult::Unknown;
#else
    if (!libKernel_) return CompareResult::Unknown;

    // rational-algebraic inside interval: eval defining poly at q
    if (a.isRational() && b.isAlgebraic()) {
        const auto& fCoeffs = getUni(b.root.definingPoly);
        mpq_class val = evalUniAtRational(fCoeffs, a.rational);
        if (val == 0) return CompareResult::Equal;

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
        const auto& fCoeffs = getUni(a.root.definingPoly);
        mpq_class val = evalUniAtRational(fCoeffs, b.rational);
        if (val == 0) return CompareResult::Equal;

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
#ifndef ZOLVER_HAS_LIBPOLY
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
#ifndef ZOLVER_HAS_LIBPOLY
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

} // namespace zolver
