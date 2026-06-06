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

// P6-S3 preemptive diagnose: env-gated counters at the SingleCellProjection
// step-0/step-1 round-trip and unitKey sites. Default no-op — only emits a
// dump line when XOLVER_NRA_CAC_INSTR is set. After S1+S1b, this measures the
// residual cost not covered by kernel-level hash-cons (RP→PolyId driver setup,
// fromPolyId reconversion, unitKey string-key serialize) so S3 ship vs route
// is decided from data, not from hypothesis.
struct CacInstr {
    uint64_t cellCalls = 0;
    uint64_t leafCalls = 0;
    uint64_t step0ToPrim = 0;
    uint64_t step0FromPolyId = 0;
    uint64_t step0UnitKey = 0;
    uint64_t step0UnitKeyChars = 0;   // running sum to approximate avg key length
    uint64_t step1ToPrim = 0;
    uint64_t step1ResidualToPrim = 0;
    uint64_t leafToPrim = 0;
    ~CacInstr() {
        if (std::getenv("XOLVER_NRA_CAC_INSTR") == nullptr) return;
        const double avgKey = step0UnitKey ? static_cast<double>(step0UnitKeyChars) / static_cast<double>(step0UnitKey) : 0.0;
        std::fprintf(stderr,
            "[XOLVER_NRA_CAC_INSTR] cells=%llu leaves=%llu | step0: toPrim=%llu fromPolyId=%llu unitKey=%llu(avg=%.1f chars) | step1: toPrim=%llu residualToPrim=%llu | leaf: toPrim=%llu\n",
            (unsigned long long)cellCalls, (unsigned long long)leafCalls,
            (unsigned long long)step0ToPrim, (unsigned long long)step0FromPolyId,
            (unsigned long long)step0UnitKey, avgKey,
            (unsigned long long)step1ToPrim, (unsigned long long)step1ResidualToPrim,
            (unsigned long long)leafToPrim);
    }
};
static CacInstr g_cacInstr;

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
    ++g_cacInstr.step0UnitKey;
    g_cacInstr.step0UnitKeyChars += key.size();
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
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue) {

    CellResult out;   // supported == false by default
    if (!algebra || !kernel) return out;
    ++g_cacInstr.cellCalls;

    static const bool diag = std::getenv("XOLVER_NRA_CAC_DIAG") != nullptr;
    auto bail = [&](const char* why) -> CellResult {
        if (diag) {
            std::ofstream st("/tmp/cac_cell.txt", std::ios::app);
            st << "[CELL] unsupported why=" << why
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
            ++g_cacInstr.step0ToPrim;
            auto norm = rp.toPrimitiveInteger(*kernel);
            if (!norm.ok()) return bail("toPrim");
            if (kernel->isConstant(norm.poly)) continue;
            // A constraint's NULLIFICATION is a whole-poly property, so the vanish
            // decision (step 1) must see the ORIGINAL poly — not its factors.
            // Square-free factoring splits a poly that vanishes on the fiber into a
            // vanishing factor and (possibly) NON-vanishing ones: e.g. (x-1)*y at
            // x=1 → {(x-1) [vanishes], y [does NOT]}. The leaf skip ("≡0 on the
            // fiber ⇒ uniform truth ⇒ no boundary") would then fire only for the
            // vanishing factor while `y` wrongly adds a boundary y=0 (cell too
            // small). So only factor polys that do NOT vanish: over an integral
            // domain ∏fᵢ≡0 ⇔ some fᵢ≡0, hence a non-vanishing poly has no vanishing
            // factor → factoring is sound and the dedup perf win still applies to
            // the dominant non-vanishing projection polys. Vanishing polys pass
            // through WHOLE; step 1 decides skip (leaf) vs Lazard-residual
            // (non-leaf) on the original constraint. (Rational prefix only:
            // vanishesAtPrefix is Unknown for algebraic prefixes, where factoring
            // stays at-worst conservative — cell too small, never too big — so the
            // covering remains sound, just possibly finer.)
            if (!prefixHasAlgebraic &&
                algebra->vanishesAtPrefix(norm.poly, prefix, var) == VanishResult::Vanishes) {
                reduced.push_back(rp);
                continue;
            }
            for (PolyId f : kernel->squareFreeFactors(norm.poly)) {
                if (kernel->isConstant(f)) continue;
                ++g_cacInstr.step0FromPolyId;
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
        ++g_cacInstr.step1ToPrim;
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
            // FAST PATH (cacheable algebraic numbers): if the boundary poly provably
            // keeps full degree in `var` at the prefix — its leading coefficient (in
            // `var`) is DEFINITE-NONZERO there — it does NOT nullify, so libpoly's
            // NATIVE isolation is complete + sound AND ~750x faster than the hand-
            // rolled resultant-Norm here (it reuses the persistent assignment's refined
            // algebraic numbers instead of recomputing a tower Norm per cell). A
            // possibly-nullifying poly (leading coeff zero/undecided) or a native crash
            // falls back to the nullification-aware Norm/Tower path (fail-closed).
            {
                RationalPolynomial lc = rp.leadingCoefficient(var);
                auto lcN = lc.toPrimitiveInteger(*kernel);
                if (lcN.ok()) {
                    const Sign ls = algebra->signAt(lcN.poly, prefix);
                    if (ls == Sign::Pos || ls == Sign::Neg) {   // non-nullifying ⇒ native is complete
                        RootSet ra = algebra->isolateRealRootsAlgebraic(pid, prefix, var);
                        if (!ra.crashOccurred) { rs = std::move(ra); supported = true; }
                    }
                }
            }
            if (!supported) rs = algebra->isolateRealRootsViaNorm(pid, prefix, var, supported);
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
                // pid is a PROJECTION FACTOR (this is the non-leaf lifting path;
                // leaf atoms never reach here — they go through characterizeLeafAtom).
                // ≡0 does NOT mean "no boundary" — its Lazard valuation residual
                // still carries genuine lifting boundaries (cvc5 routes every char
                // poly through LazardEvaluation::isolateRealRoots and NEVER skips;
                // skipping enlarges the cell ⇒ false UNSAT). Recover the residual
                // via the rational-coordinate Lazard valuation, then isolate ITS
                // roots. This is lifting-boundary recovery ONLY, never atom truth —
                // and it is the SOLE place residual→boundary is allowed.
                RationalPolynomial residual = lazardResidualRational(rp, prefix);
                residual.normalize();
                if (residual.isZero() || !residual.contains(var)) continue;   // no var-boundary
                for (VarId v : residual.variables())
                    if (v != var) return bail("residual-stray-var");          // fail-closed
                ++g_cacInstr.step1ResidualToPrim;
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

LeafCellResult characterizeLeafAtom(
    LibpolyBackend* algebra, PolynomialKernel* kernel,
    const RationalPolynomial& poly, Relation rel,
    const SamplePoint& prefix, VarId var, const RealAlg& sampleValue) {

    LeafCellResult out;   // supported == false by default
    if (!algebra || !kernel) return out;
    ++g_cacInstr.leafCalls;
    ++g_cacInstr.leafToPrim;

    auto norm = poly.toPrimitiveInteger(*kernel);
    if (!norm.ok()) return out;
    const PolyId pid = norm.poly;

    // (a) TRUTH PATH — the atom's exact truth AT the sample (full assignment).
    //     An Unknown sign is fail-closed (⇒ supported=false ⇒ caller Unknown).
    SamplePoint full = prefix;
    full.push(var, sampleValue);
    const Sign sSample = algebra->signAt(pid, full);
    if (sSample == Sign::Unknown) return out;
    out.holdsAtSample = relationHolds(sSample, rel);

    // A constant atom (no var, no remaining lower vars) is globally uniform.
    if (kernel->isConstant(pid)) {
        out.truth = out.holdsAtSample ? LeafTruth::UniformTrue : LeafTruth::UniformFalse;
        out.interval = CacInterval::all();
        out.supported = true;
        return out;
    }

    // (b) BOUNDARY PATH — does the atom NULLIFY in `var` on this fiber?
    bool prefixAlg = false;
    for (const auto& pv : prefix.values) if (pv.isAlgebraic()) { prefixAlg = true; break; }
    if (!prefixAlg) {
        // RATIONAL prefix: vanishesAtPrefix is exact + decisive.
        const VanishResult vr = algebra->vanishesAtPrefix(pid, prefix, var);
        if (vr == VanishResult::Unknown) return out;     // fail-closed ⇒ caller Unknown
        if (vr == VanishResult::Vanishes) {
            // poly ≡ 0 in `var` on the fiber ⇒ UNIFORM truth, decided by (0 rel 0).
            // NO var-boundary (the valuation residual is a LIFTING boundary, never a
            // leaf atom's truth, so it is NOT injected here). UniformFalse ⇒ the whole
            // fiber is infeasible; the caller excludes the entire axis. (signAt at the
            // sample agrees: sSample == Zero ⇒ holdsAtSample == relationHolds(Zero,rel).)
            out.truth = relationHolds(Sign::Zero, rel) ? LeafTruth::UniformTrue
                                                       : LeafTruth::UniformFalse;
            out.interval = CacInterval::all();
            out.supported = true;
            return out;
        }
        // NotVanishes ⇒ fall through to the NonUniform isolation below.
    } else {
        // ALGEBRAIC prefix: vanishesAtPrefix returns Unknown for ANY algebraic prefix
        // by design (LibpolyBackend), so consulting it here BAILED before the
        // algebraic-capable isolation was ever reached — the same "unreachable-tower-
        // path ordering bug" already fixed in intervalFromCharacterization (the leaf
        // path still had it: hong dies at the first algebraic coordinate, var=3).
        // Decide nullification SOUNDLY from the leading coefficient's sign at the
        // prefix instead:
        //   - poly structurally var-free ⇒ uniform truth (holdsAtSample).
        //   - leading coeff (in `var`) DEFINITE-NONZERO at the prefix ⇒ poly|prefix
        //     keeps full degree ⇒ a nonzero univariate ⇒ does NOT nullify ⇒
        //     NonUniform: fall through to the exact isolation below (itself
        //     fail-closed on any inconclusive backend step ⇒ never a wrong cell).
        //   - leading coeff Zero/Unknown ⇒ degree may drop / nullify; cannot cheaply
        //     decide ⇒ fail-closed (return unsupported).
        // Scan the var-coefficients HIGH→LOW (each a poly in the lower vars):
        //   first DEFINITE-NONZERO coeff at degree ≥1 ⇒ poly keeps a genuine var-
        //     dependence ⇒ NonUniform (its roots delineate) ⇒ isolate below;
        //   ALL degree-≥1 coeffs definite-ZERO ⇒ poly|prefix is CONSTANT in var ⇒
        //     uniform truth, decided by signAt at the sample (holdsAtSample) — this
        //     is hong's `x0·x1·x2 > 1` at x1=0: lead coeff x0·x1 vanishes but the
        //     constant term −1 ≠ 0, so it is constant (−1), UniformFalse;
        //   any coeff UNKNOWN before a nonzero is found ⇒ fail-closed (unsupported).
        const std::vector<RationalPolynomial> vcoeffs = poly.coefficients(var);  // index = degree
        bool nonUniform = false;
        for (int d = static_cast<int>(vcoeffs.size()) - 1; d >= 1 && !nonUniform; --d) {
            RationalPolynomial c = vcoeffs[d];
            c.normalize();
            if (c.isZero()) continue;
            auto cN = c.toPrimitiveInteger(*kernel);
            if (!cN.ok()) return out;                       // fail-closed
            const Sign cs = algebra->signAt(cN.poly, prefix);
            if (cs == Sign::Pos || cs == Sign::Neg) { nonUniform = true; break; }  // degree-d term survives
            if (cs == Sign::Unknown) return out;            // fail-closed
            // Zero ⇒ this term vanishes at the prefix; keep scanning lower degrees.
        }
        if (!nonUniform) {
            // Constant in var at the prefix ⇒ uniform truth at the sample.
            out.truth = out.holdsAtSample ? LeafTruth::UniformTrue : LeafTruth::UniformFalse;
            out.interval = CacInterval::all();
            out.supported = true;
            return out;
        }
        // A genuine var-dependence survives ⇒ NonUniform isolation below.
    }

    // NotVanishes (or algebraic non-nullifying): poly|prefix is a nonzero univariate. Its real roots delineate
    // the maximal sign-invariant cell around the sample (exact isolation). If it
    // has NO var-boundary (constant-nonzero in var on the fiber ⇒ cell == ℝ), the
    // atom is still uniform; otherwise its sign changes across roots ⇒ NonUniform.
    const CellResult cell = intervalFromCharacterization(algebra, kernel, {poly},
                                                         prefix, var, sampleValue);
    if (!cell.supported) return out;
    out.interval = cell.interval;
    const bool wholeAxis = cell.interval.lo.isNegInf() && cell.interval.hi.isPosInf();
    out.truth = wholeAxis ? (out.holdsAtSample ? LeafTruth::UniformTrue : LeafTruth::UniformFalse)
                          : LeafTruth::NonUniform;
    out.supported = true;
    return out;
}

#else  // !XOLVER_HAS_LIBPOLY

CellResult intervalFromCharacterization(
    LibpolyBackend*, PolynomialKernel*,
    const std::vector<RationalPolynomial>&, const SamplePoint&, VarId, const RealAlg&) {
    return {};   // unsupported without the algebra backend
}

LeafCellResult characterizeLeafAtom(
    LibpolyBackend*, PolynomialKernel*,
    const RationalPolynomial&, Relation, const SamplePoint&, VarId, const RealAlg&) {
    return {};   // unsupported without the algebra backend
}

#endif

} // namespace xolver
