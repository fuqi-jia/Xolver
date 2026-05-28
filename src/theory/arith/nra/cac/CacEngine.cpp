#include "theory/arith/nra/cac/CacEngine.h"

#include "theory/arith/nra/cac/SingleCellProjection.h"

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <utility>

#ifdef XOLVER_HAS_LIBPOLY
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/core/CdcacCommon.h"   // Sign
#include "theory/arith/poly/PolynomialKernel.h"
#endif

namespace xolver {

CacEngine::CacEngine(LibpolyBackend* algebra, PolynomialKernel* kernel,
                     std::vector<VarId> varOrder, std::vector<CacConstraint> constraints,
                     Config cfg)
    : algebra_(algebra), kernel_(kernel), varOrder_(std::move(varOrder)),
      cons_(std::move(constraints)), cfg_(cfg) {
#ifdef XOLVER_HAS_LIBPOLY
    if (kernel_) {
        consPoly_.reserve(cons_.size());
        for (const auto& c : cons_) {
            auto norm = c.poly.toPrimitiveInteger(*kernel_);   // scale > 0, relation-preserving
            if (!norm.ok()) { buildOk_ = false; consPoly_.push_back(NullPoly); }
            else consPoly_.push_back(norm.poly);
        }
    } else {
        buildOk_ = false;
    }
#else
    buildOk_ = false;
#endif
}

CacEngine::CacEngine(LibpolyBackend* algebra, PolynomialKernel* kernel,
                     std::vector<VarId> varOrder, std::vector<CacConstraint> constraints)
    : CacEngine(algebra, kernel, std::move(varOrder), std::move(constraints), Config{}) {}

#ifdef XOLVER_HAS_LIBPOLY

namespace {
bool relationHolds(Sign s, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return s == Sign::Zero;
        case Relation::Neq: return s != Sign::Zero;   // caller has excluded Sign::Unknown
        case Relation::Lt:  return s == Sign::Neg;
        case Relation::Leq: return s == Sign::Neg || s == Sign::Zero;
        case Relation::Gt:  return s == Sign::Pos;
        case Relation::Geq: return s == Sign::Pos || s == Sign::Zero;
    }
    return false;
}

// Covering sample (RealValue) → engine sample (RealAlg). Rational is exact; an
// algebraic value is rebuilt from its defining poly (low→high) + isolating
// interval into the engine's UniPolyId-handle form (high→low).
RealAlg toRealAlg(LibpolyBackend& algebra, const RealValue& v) {
    if (v.isRational()) return RealAlg::fromRational(v.asRational());
    const AlgebraicNumber& a = v.asAlgebraic();
    std::vector<mpz_class> hiLo(a.coefficients.rbegin(), a.coefficients.rend());
    const UniPolyId up = algebra.allocUni(hiLo);

    // CRITICAL: algebraic signAt picks roots[rootIndex] (LibpolyBackend ~:1043),
    // so the rootIndex MUST identify the right root. The RealValue→RealAlg
    // round-trip dropped it (RealValue has no rootIndex), so a hardcoded 0 picks
    // the WRONG root (e.g. -√2 for √2) → false verdicts. Recover it: isolate the
    // defining poly's roots and return the one whose isolating interval matches
    // the RealValue's [a.lower, a.upper] (its correct rootIndex + native form).
    RootSet rs = algebra.isolateRealRoots(up);
    for (const auto& r : rs.roots) {
        if (r.isRational()) {
            if (a.lower <= r.rational && r.rational <= a.upper) return r;
        } else {
            // overlapping isolating intervals ⇒ same root.
            if (r.root.lower <= a.upper && a.lower <= r.root.upper) return r;
        }
    }
    // Fallback (no match — should not happen): hand-built, rootIndex 0.
    AlgebraicRoot ar;
    ar.definingPoly = up;
    ar.rootIndex = 0;
    ar.lower = a.lower;
    ar.upper = a.upper;
    return RealAlg::fromAlgebraic(std::move(ar));
}
} // namespace

CacEngine::CoverOut CacEngine::getUnsatCover(int level, SamplePoint& sample) {
    CoverOut out;
    if (level > maxDepth_) maxDepth_ = level;
    if (++nodes_ > cfg_.maxNodes) { out.status = CacStatus::Unknown; lastUnknown_ = "node-budget"; return out; }

    const int n = static_cast<int>(varOrder_.size());
    const VarId var = varOrder_[level];
    const bool isLeaf = (level == n - 1);

    CacCovering cov;
    std::vector<RationalPolynomial> levelChar;   // delineators of this level's covering
    long cells = 0;

    while (auto sOpt = cov.sampleUncovered()) {   // nullopt ⇒ covering gap-free
        if (++cells > cfg_.maxCellsPerLevel) { out.status = CacStatus::Unknown; lastUnknown_ = "cell-budget"; return out; }
        const RealAlg s_i = toRealAlg(*algebra_, *sOpt);
        sample.push(var, s_i);

        std::vector<RationalPolynomial> cellBoundaries;

        if (isLeaf) {
            bool allHold = true;
            bool anyUnknown = false;
            std::vector<RationalPolynomial> violated;
            for (size_t ci = 0; ci < cons_.size(); ++ci) {
                const Sign s = algebra_->signAt(consPoly_[ci], sample);
                if (s == Sign::Unknown) { anyUnknown = true; break; }
                if (!relationHolds(s, cons_[ci].rel)) violated.push_back(cons_[ci].poly), allHold = false;
            }
            if (std::getenv("XOLVER_NRA_CAC_DIAG")) {
                std::ofstream st("/tmp/cac_leaf.txt", std::ios::app);
                st << "[LEAF] var=" << var << " sample=" << (s_i.isRational() ? s_i.rational.get_str() : "alg")
                   << " allHold=" << allHold << " violated=" << violated.size()
                   << " anyUnknown=" << anyUnknown << "\n";
                st.flush();
            }
            if (anyUnknown) { sample.pop(); out.status = CacStatus::Unknown; lastUnknown_ = "signAt-unknown"; return out; }
            if (allHold)    { satModel_ = sample; sample.pop(); out.status = CacStatus::Sat; return out; }
            cellBoundaries = std::move(violated);
        } else {
            CoverOut rec = getUnsatCover(level + 1, sample);
            if (rec.status == CacStatus::Sat)     { sample.pop(); out.status = CacStatus::Sat; return out; }
            if (rec.status == CacStatus::Unknown) { sample.pop(); out.status = CacStatus::Unknown; return out; }
            // rec UNSAT: project its characterization down, eliminating var_{level+1}.
            // `sample` holds vars[0..level]; the required coefficients (in those
            // vars) are evaluated against it (McCallum sample-aware projection).
            CharacterizationResult ch = characterize(rec.charPolys, varOrder_[level + 1], kernel_, &sample);
            if (!ch.complete) { sample.pop(); out.status = CacStatus::Unknown; lastUnknown_ = "characterize-incomplete"; return out; }
            cellBoundaries = std::move(ch.downwardPolys);
        }

        // Cell on var's axis around s_i, from boundary polys isolated at the prefix.
        SamplePoint prefix = sample;
        prefix.pop();                                   // vars[0..level-1]
        // Leaf boundary polys are original constraints: a constraint constant on
        // the fiber (vanishes in var) has no boundary ⇒ skip is sound. Non-leaf
        // characterization polys must not skip vanishing (nullification ⇒ Unknown).
        const CellResult cr = intervalFromCharacterization(algebra_, kernel_, cellBoundaries,
                                                           prefix, var, s_i, /*skipVanishing=*/isLeaf);
        sample.pop();                                   // restore for next iteration
        if (!cr.supported) { out.status = CacStatus::Unknown; lastUnknown_ = isLeaf ? "interval-unsupported-leaf" : "interval-unsupported-nonleaf"; return out; }
        cov.add(cr.interval);
        for (auto& p : cellBoundaries) levelChar.push_back(std::move(p));
    }

    // The covering is gap-free over ℝ (loop exited) and every cell was a
    // `supported` interval from a complete characterization ⇒ sound UNSAT.
    out.status = CacStatus::Unsat;
    out.charPolys = std::move(levelChar);
    return out;
}

CacResult CacEngine::solve() {
    CacResult res;
    if (!buildOk_ || !algebra_ || !kernel_ || varOrder_.empty()) {
        res.status = CacStatus::Unknown;
        return res;
    }
    SamplePoint sample;
    const CoverOut o = getUnsatCover(0, sample);
    res.status = o.status;
    if (o.status == CacStatus::Sat) res.model = satModel_;
    return res;
}

#else  // !XOLVER_HAS_LIBPOLY

CacEngine::CoverOut CacEngine::getUnsatCover(int, SamplePoint&) {
    CoverOut o; o.status = CacStatus::Unknown; return o;
}
CacResult CacEngine::solve() { CacResult r; r.status = CacStatus::Unknown; return r; }

#endif

} // namespace xolver
