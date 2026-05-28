#include "theory/arith/nra/cac/SingleCellProjection.h"

#include "theory/arith/nra/projection/LazardProjectionOperator.h"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <string>
#include <unordered_set>

#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/core/CdcacCommon.h"   // CompareResult, VanishResult
#include "theory/arith/poly/PolynomialKernel.h"
#endif

namespace xolver {

namespace {
// Canonical key (up to a rational unit) for deduping output polynomials, so a
// coefficient and a discriminant that are proportional collapse to one boundary.
std::string unitKey(RationalPolynomial p) {
    p.normalize();
    if (!p.isZero()) {
        const mpq_class lead = p.terms().rbegin()->second;
        if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
    }
    std::string key;
    for (const auto& [mon, coeff] : p.terms()) {
        key += coeff.get_str() + ":";
        for (const auto& [v, e] : mon) key += std::to_string(v) + "^" + std::to_string(e) + ";";
        key += "|";
    }
    return key;
}
} // namespace

CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel) {
    CharacterizationResult out;
    std::unordered_set<std::string> seenBoundary, seenDownward;

    // Inputs already FREE of elimVar are at a lower level — pass them straight
    // through to downwardPolys (eliminating elimVar from them is a no-op; the
    // Lazard operator emits nothing for them, so they must be retained here, NOT
    // dropped). Only inputs containing elimVar are projected.
    std::vector<RationalPolynomial> withElim;
    for (const auto& cp : cellPolys) {
        RationalPolynomial p = cp;
        p.normalize();
        if (p.isZero() || p.isConstant()) continue;
        if (p.degree(elimVar) >= 1) {
            withElim.push_back(std::move(p));
        } else if (seenDownward.insert(unitKey(p)).second) {
            out.downwardPolys.push_back(std::move(p));
        }
    }

    if (!withElim.empty()) {
        LazardOpResult r = lazardProjectStep(withElim, elimVar,
                                             LazardProjectionConfig(), kernel);
        if (!r.complete) {
            out.complete = false;
            return out;   // caller ⇒ Unknown; never UNSAT on an incomplete characterization
        }
        for (const auto& item : r.items) {
            RationalPolynomial p = item.poly;
            p.normalize();
            if (p.isZero() || p.isConstant()) continue;
            if (p.degree(elimVar) >= 1) {
                if (seenBoundary.insert(unitKey(p)).second) out.boundaryPolys.push_back(std::move(p));
            } else if (seenDownward.insert(unitKey(p)).second) {
                out.downwardPolys.push_back(std::move(p));
            }
        }
    }
    return out;
}

#ifdef XOLVER_HAS_LIBPOLY

namespace {
// Engine RealAlg → util RealValue (for CacInterval endpoints). Algebraic roots
// carry their defining univariate by handle; getUni returns it high→low degree,
// while RealValue::AlgebraicNumber wants low→high (coefficients[i] = coeff x^i).
RealValue toRealValue(LibpolyBackend& algebra, const RealAlg& r) {
    if (r.isRational()) return RealValue::fromMpq(r.rational);
    const std::vector<mpz_class>& hiLo = algebra.getUni(r.root.definingPoly);
    AlgebraicNumber a;
    a.coefficients.assign(hiLo.rbegin(), hiLo.rend());
    a.lower = r.root.lower;
    a.upper = r.root.upper;
    a.lowerOpen = true;
    a.upperOpen = true;
    return RealValue::fromAlgebraic(std::move(a));
}
} // namespace

CellResult intervalFromCharacterization(
    LibpolyBackend* algebra, PolynomialKernel* kernel,
    const std::vector<RationalPolynomial>& boundaryPolys,
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue,
    bool skipVanishing) {

    CellResult out;   // supported == false by default
    if (!algebra || !kernel) return out;

    static const bool diag = std::getenv("XOLVER_NRA_CAC_DIAG") != nullptr;
    auto bail = [&](const char* why) -> CellResult {
        if (diag) {
            std::ofstream st("/tmp/cac_cell.txt", std::ios::app);
            st << "[CELL] unsupported why=" << why << " leaf=" << skipVanishing
               << " nbound=" << boundaryPolys.size() << "\n";
            st.flush();
        }
        return out;
    };

    bool prefixHasAlgebraic = false;
    for (const auto& v : prefix.values) if (v.isAlgebraic()) { prefixHasAlgebraic = true; break; }

    // 1. Collect this level's delineating roots at the prefix.
    std::vector<RealAlg> roots;
    for (const auto& rp : boundaryPolys) {
        auto norm = rp.toPrimitiveInteger(*kernel);
        if (!norm.ok()) return bail("toPrim");
        const PolyId pid = norm.poly;
        if (kernel->isConstant(pid)) continue;            // no boundary
        const VanishResult vr = algebra->vanishesAtPrefix(pid, prefix, var);
        if (vr == VanishResult::Unknown) return bail("vanish-unknown");
        if (vr == VanishResult::Vanishes) {
            if (skipVanishing) continue;                  // leaf constraint: no var-boundary
            return bail("vanish-nonleaf");                // non-leaf nullification ⇒ Unknown
        }

        const UniPolyId up = algebra->specializeToUnivariate(pid, prefix, var);
        RootSet rs;
        if (up == NullUniPolyId) {
            if (!prefixHasAlgebraic) return bail("specialize-fail-rational");
            bool supported = false;
            rs = algebra->isolateRealRootsViaNorm(pid, prefix, var, supported);
            if (!supported) rs = algebra->isolateRealRootsViaTower(pid, prefix, var, supported);
            if (!supported) return bail("algebraic-isolation-unsupported");
        } else {
            rs = algebra->isolateRealRoots(up);
            if (rs.crashOccurred) return bail("isolate-crash");
            if (!algebra->validateRootIsolation(up, rs)) return bail("isolate-invalid");
        }
        for (auto& r : rs.roots) roots.push_back(std::move(r));
    }

    // 2. Sort + dedup (exact algebraic comparison; any inconclusive ⇒ Unknown).
    bool cmpFail = false;
    std::sort(roots.begin(), roots.end(), [&](const RealAlg& a, const RealAlg& b) {
        const CompareResult c = algebra->compareRealAlg(a, b);
        if (c == CompareResult::Unknown) cmpFail = true;
        return c == CompareResult::Less;
    });
    if (cmpFail) return bail("sort-compare-unknown");
    std::vector<RealAlg> distinct;
    for (auto& r : roots) {
        if (!distinct.empty()) {
            const CompareResult c = algebra->compareRealAlg(distinct.back(), r);
            if (c == CompareResult::Unknown) return bail("dedup-compare-unknown");
            if (c == CompareResult::Equal) continue;
        }
        distinct.push_back(std::move(r));
    }

    // 3. Locate the sample among the sorted distinct roots.
    int loIdx = -1, hiIdx = -1, ptIdx = -1;
    for (int i = 0; i < static_cast<int>(distinct.size()); ++i) {
        const CompareResult c = algebra->compareRealAlg(distinct[i], sampleValue);
        if (c == CompareResult::Unknown) return bail("locate-compare-unknown");
        if (c == CompareResult::Less) { loIdx = i; }
        else if (c == CompareResult::Equal) { ptIdx = i; break; }
        else { hiIdx = i; break; }   // first root > sample
    }

    // 4. Build the cell (RealValue endpoints).
    if (ptIdx >= 0) {
        out.interval = CacInterval::point(toRealValue(*algebra, distinct[ptIdx]));
    } else {
        ExtendedRealValue lo = (loIdx < 0)
            ? ExtendedRealValue::negInf()
            : ExtendedRealValue::finite(toRealValue(*algebra, distinct[loIdx]));
        ExtendedRealValue hi = (hiIdx < 0)
            ? ExtendedRealValue::posInf()
            : ExtendedRealValue::finite(toRealValue(*algebra, distinct[hiIdx]));
        out.interval = CacInterval::make(std::move(lo), std::move(hi), true, true);
    }
    out.supported = true;
    return out;
}

#else  // !XOLVER_HAS_LIBPOLY

CellResult intervalFromCharacterization(
    LibpolyBackend*, PolynomialKernel*,
    const std::vector<RationalPolynomial>&, const SamplePoint&, VarId, const RealAlg&, bool) {
    return {};   // unsupported without the algebra backend
}

#endif

} // namespace xolver
