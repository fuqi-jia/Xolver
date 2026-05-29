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
// McCallum required coefficients of f w.r.t. elimVar (cvc5 requiredCoefficients-
// Original): the var-coefficients top-down; add each non-constant one; stop at
// the first that is constant or provably nonzero at the sample. nullptr sample ⇒
// add all non-constant coefficients (conservative). All in lower variables.
std::vector<RationalPolynomial> requiredCoefficients(const RationalPolynomial& f,
                                                     VarId elimVar,
                                                     const SamplePoint* sample) {
    std::vector<RationalPolynomial> out;
    std::vector<RationalPolynomial> coeffs = f.coefficients(elimVar);  // index i = coeff of elimVar^i
    for (int deg = static_cast<int>(coeffs.size()) - 1; deg >= 0; --deg) {
        RationalPolynomial c = coeffs[deg];
        c.normalize();
        if (c.isZero()) continue;          // gap coefficient — not a boundary
        if (c.isConstant()) break;         // nonzero constant ⇒ degree fixed ⇒ done
        out.push_back(c);                  // required (a lower-level boundary)
        if (sample) {
            // Provably nonzero at the sample? Substitute the rational coords; if
            // it collapses to a nonzero constant, the degree does not drop here.
            RationalPolynomial e = c;
            for (size_t i = 0; i < sample->varOrder.size(); ++i) {
                if (sample->values[i].isRational())
                    e = e.substituteRational(sample->varOrder[i], sample->values[i].rational);
            }
            e.normalize();
            if (e.isConstant() && !e.isZero()) break;   // nonzero-at-sample ⇒ stop
            // else (vanishes or algebraic/undecided): keep going (sound: more coeffs)
        }
    }
    return out;
}

} // namespace

CharacterizationResult characterize(const std::vector<RationalPolynomial>& cellPolys,
                                    VarId elimVar,
                                    PolynomialKernel* kernel,
                                    const SamplePoint* sample) {
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
        // McCallum required coefficients (sample-aware): completes the projection
        // for nullification — the LC/TC the Lazard step emits is insufficient
        // (caused false-UNSAT). A superset of LC/TC, so adding it is sound.
        for (const auto& f : withElim) {
            for (auto& c : requiredCoefficients(f, elimVar, sample)) {
                if (c.degree(elimVar) >= 1) continue;   // (defensive: coeffs are in lower vars)
                if (seenDownward.insert(unitKey(c)).second) out.downwardPolys.push_back(std::move(c));
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

// Exact division of p (viewed univariate in xi) by the linear factor (xi - ai),
// ai rational. Returns {quotient, divisible}: divisible iff (xi - ai) | p with
// zero remainder (Horner synthetic division over the multivariate coefficients).
std::pair<RationalPolynomial, bool> divideByLinearExact(const RationalPolynomial& p,
                                                        VarId xi, const mpq_class& ai) {
    std::vector<RationalPolynomial> c = p.coefficients(xi);   // c[j] = coeff of xi^j
    const int d = static_cast<int>(c.size()) - 1;
    if (d < 1) return {p, false};                             // no xi ⇒ not divisible
    std::vector<RationalPolynomial> b(d);
    b[d - 1] = c[d];
    for (int j = d - 1; j >= 1; --j) {
        RationalPolynomial t = b[j];
        t *= ai;
        b[j - 1] = c[j] + t;
    }
    RationalPolynomial t0 = b[0];
    t0 *= ai;
    RationalPolynomial rem = c[0] + t0;
    rem.normalize();
    if (!rem.isZero()) return {p, false};
    RationalPolynomial quot;
    for (int j = 0; j < d; ++j) {
        // j==0 is the xi^0 (constant-in-xi) term; fromVar(xi,0,·) returns ZERO by
        // design (exponents must be >0), so add b[0] directly — otherwise the
        // constant quotient term is silently dropped and the residual collapses.
        if (j == 0) quot += b[0];
        else quot += b[j] * RationalPolynomial::fromVar(xi, j, mpq_class(1));
    }
    quot.normalize();
    return {quot, true};
}

// Lazard valuation residual of p at a RATIONAL prefix (cvc5 LazardEvaluation::
// reducePolynomial specialized to rational coordinates: the CoCoA tower reduction
// degenerates to iterated vanishing-factor division). Processes the prefix coords
// IN ORDER (the elimination order): for each xi=ai, divide out (xi-ai) to its full
// multiplicity, then substitute xi=ai. The result is the residual whose real roots
// are the genuine LIFTING boundaries a nullified projection factor still imposes
// (NEVER atom truth). Sound: exact rational arithmetic, no algebraic extension ⇒
// no spurious/conjugate roots (so cvc5's spurious-root filter is a no-op here).
RationalPolynomial lazardResidualRational(RationalPolynomial p, const SamplePoint& prefix) {
    for (size_t i = 0; i < prefix.varOrder.size(); ++i) {
        if (!prefix.values[i].isRational()) return RationalPolynomial();   // caller guards rational-only
        const VarId xi = prefix.varOrder[i];
        const mpq_class ai = prefix.values[i].rational;
        p.normalize();
        while (p.contains(xi)) {
            auto qd = divideByLinearExact(p, xi, ai);
            if (!qd.second) break;
            p = std::move(qd.first);
            p.normalize();
        }
        p = p.substituteRational(xi, ai);
        p.normalize();
    }
    return p;
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

    // 0. WITNESS-BASED CHARACTERIZATION REDUCTION: replace each boundary poly by
    //    its SQUARE-FREE FACTORS and DEDUP across all boundary polys. This is
    //    root-preserving (the factors' real roots = the poly's real roots, and
    //    specialization commutes with the product: p(prefix,var)=∏ f_i(prefix,var)),
    //    so the cell boundaries are IDENTICAL — sound. It only removes provably
    //    redundant work: shared factors (resultants/discriminants of high-degree
    //    meti-tarski polys overlap heavily) are specialized+isolated ONCE instead
    //    of once per containing poly, cutting the dominant per-cell cost. NO
    //    heuristic drop — only exact duplicates of square-free factors are removed.
    std::vector<RationalPolynomial> reduced;
    {
        std::unordered_set<std::string> seenFac;
        for (const auto& rp : boundaryPolys) {
            auto norm = rp.toPrimitiveInteger(*kernel);
            if (!norm.ok()) return bail("toPrim");
            if (kernel->isConstant(norm.poly)) continue;
            for (PolyId f : kernel->squareFreeFactors(norm.poly)) {
                if (kernel->isConstant(f)) continue;
                auto frp = RationalPolynomial::fromPolyId(f, *kernel);
                if (!frp) { reduced.push_back(rp); continue; }   // fail-safe: keep the whole poly
                frp->normalize();
                if (seenFac.insert(unitKey(*frp)).second) reduced.push_back(std::move(*frp));
            }
        }
    }

    // 1. Collect this level's delineating roots at the prefix.
    std::vector<RealAlg> roots;
    for (const auto& rp : reduced) {
        auto norm = rp.toPrimitiveInteger(*kernel);
        if (!norm.ok()) return bail("toPrim");
        const PolyId pid = norm.poly;
        if (kernel->isConstant(pid)) continue;            // no boundary
        RootSet rs;
        if (prefixHasAlgebraic) {
            // ALGEBRAIC prefix: route to the more-capable tower path, which
            // isolates roots AND handles nullification via the [H3] valuation
            // (lifting-boundary recovery — NEVER atom truth), gated FAIL-CLOSED by
            // `supported` (any inconclusive sub-step ⇒ supported=false ⇒ caller
            // Unknown, never UNSAT). We do NOT consult vanishesAtPrefix here: it
            // returns Unknown for ANY algebraic prefix by design (LibpolyBackend),
            // a cheap UNSUPPORTED check that, placed first, used to bail before
            // this path was even reached (the unreachable-tower-path ordering bug
            // found in the audit). The tower path is MORE capable, not total — it
            // still has its own unsupported branches (→ bail), so this is a
            // reachability fix, not a completeness claim.
            // A boundary poly with NO dependence on `var` once the rational prefix
            // coords are fixed contributes no boundary on the lift axis (it is
            // constant along `var` at this prefix). Skip it — sound for leaf
            // (uniform truth via signAt → whole fiber handled) and non-leaf (no
            // delineation). This mirrors the rational fiber-constant skip; without
            // it the tower path bails "p1-no-mainVar" for an outer-variable-only
            // constraint at an algebraic leaf (the CONVOI2 gap), losing the case.
            {
                RationalPolynomial pr = rp;
                for (size_t i = 0; i < prefix.numVars(); ++i)
                    if (prefix.values[i].isRational())
                        pr = pr.substituteRational(prefix.varOrder[i], prefix.values[i].rational);
                pr.normalize();
                if (!pr.contains(var)) continue;   // no var-boundary at this prefix
            }
            bool supported = false;
            rs = algebra->isolateRealRootsViaNorm(pid, prefix, var, supported);
            if (!supported) rs = algebra->isolateRealRootsViaTower(pid, prefix, var, supported);
            if (!supported) return bail("algebraic-isolation-unsupported");
        } else {
            // RATIONAL prefix: vanishesAtPrefix is decisive (exact substitution,
            // no algebraic coords). Vanishes ⇒ pid ≡ 0 as a polynomial in `var` on
            // the WHOLE fiber above this prefix (ALL coefficients in `var` vanish —
            // a partial leading-coefficient drop is NotVanishes, giving a lower-
            // degree but nonzero univariate that still isolates normally).
            const VanishResult vr = algebra->vanishesAtPrefix(pid, prefix, var);
            if (vr == VanishResult::Unknown) return bail("vanish-unknown");
            if (vr == VanishResult::Vanishes) {
                if (skipVanishing) {
                    // LEAF: pid is an original CONSTRAINT. ≡0 on the fiber ⇒ its
                    // truth is UNIFORM there and was already decided by signAt
                    // (pid≡0 ⇒ Sign::Zero ⇒ e.g. p>0 false on the whole fiber ⇒
                    // the entire var-axis is excluded). No var-boundary to add.
                    continue;
                }
                // NON-LEAF: pid is a PROJECTION FACTOR. ≡0 does NOT mean "no
                // boundary" — its Lazard valuation residual still carries genuine
                // lifting boundaries (cvc5 routes every char poly through
                // LazardEvaluation::isolateRealRoots and NEVER skips; skipping
                // enlarges the cell ⇒ false UNSAT). Recover the residual via the
                // rational-coordinate Lazard valuation, then isolate ITS roots.
                // This is lifting-boundary recovery ONLY, never atom truth.
                RationalPolynomial residual = lazardResidualRational(rp, prefix);
                residual.normalize();
                if (residual.isZero() || !residual.contains(var)) continue;   // no var-boundary
                for (VarId v : residual.variables())
                    if (v != var) return bail("residual-stray-var");          // fail-closed
                auto rnorm = residual.toPrimitiveInteger(*kernel);
                if (!rnorm.ok()) return bail("residual-toPrim");
                if (kernel->isConstant(rnorm.poly)) continue;
                const UniPolyId rup = algebra->specializeToUnivariate(rnorm.poly, SamplePoint{}, var);
                if (rup == NullUniPolyId) return bail("residual-specialize");
                rs = algebra->isolateRealRoots(rup);
                if (rs.crashOccurred) return bail("residual-isolate-crash");
                if (!algebra->validateRootIsolation(rup, rs)) return bail("residual-isolate-invalid");
            } else {
                const UniPolyId up = algebra->specializeToUnivariate(pid, prefix, var);
                if (up == NullUniPolyId) return bail("specialize-fail-rational");
                rs = algebra->isolateRealRoots(up);
                if (rs.crashOccurred) return bail("isolate-crash");
                if (!algebra->validateRootIsolation(up, rs)) return bail("isolate-invalid");
            }
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
    if (cmpFail) {
        // [P0 step1] Dump the exact RealAlg pairs compareRealAlg cannot order, as
        // standalone algebraic-kernel reproducers (gated XOLVER_NRA_CAC_DUMP).
        if (std::getenv("XOLVER_NRA_CAC_DUMP")) {
            std::ofstream st("/tmp/cac_repro_compare.txt", std::ios::app);
            auto ser = [&](const RealAlg& r) {
                if (r.isRational()) { st << "R " << r.rational.get_str(); return; }
                st << "A idx=" << r.root.rootIndex
                   << " lo=" << r.root.lower.get_str() << " hi=" << r.root.upper.get_str()
                   << " poly=";
                for (const auto& c : algebra->getUni(r.root.definingPoly)) st << c.get_str() << " ";
            };
            for (size_t i = 0; i < roots.size(); ++i)
                for (size_t j = i + 1; j < roots.size(); ++j)
                    if (algebra->compareRealAlg(roots[i], roots[j]) == CompareResult::Unknown) {
                        st << "PAIR\n  a: "; ser(roots[i]); st << "\n  b: "; ser(roots[j]); st << "\n";
                    }
            st.flush();
        }
        return bail("sort-compare-unknown");
    }
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
