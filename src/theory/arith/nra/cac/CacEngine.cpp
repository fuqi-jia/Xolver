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
        // Upfront representability probe: if any constraint poly cannot be
        // normalized to a primitive integer poly the engine cannot reason on it
        // ⇒ buildOk_ = false ⇒ solve() returns Unknown. (The per-atom paths
        // re-normalize on demand via characterizeLeafAtom / characterize.)
        for (const auto& c : cons_) {
            if (!c.poly.toPrimitiveInteger(*kernel_).ok()) { buildOk_ = false; break; }
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
// relationHolds(Sign, Relation) is shared in CdcacCommon.h.

// Covering sample (RealValue) → engine sample (RealAlg). Rational is exact; an
// algebraic value is rebuilt from its defining poly (low→high) + isolating
// interval into the engine's UniPolyId-handle form (high→low).
RealAlg toRealAlg(LibpolyBackend& algebra, const RealValue& v, bool& exact) {
    exact = true;
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
    //
    // Defensive (do NOT assume the round-trip is lossless): a well-formed RealValue
    // carries an ISOLATING interval bracketing exactly one root, so exactly one
    // re-isolated root must overlap. If 0 or >1 overlap, the interval is loose /
    // malformed and the match is ambiguous — we CANNOT pick the right rootIndex →
    // set exact=false so the caller fails CLOSED (→ Unknown, never a guessed root
    // that could drive a false verdict).
    RootSet rs = algebra.isolateRealRoots(up);

    auto overlaps = [&](const RealAlg& r) -> bool {
        return r.isRational()
            ? (a.lower <= r.rational && r.rational <= a.upper)
            : (r.root.lower <= a.upper && a.lower <= r.root.upper);
    };

    // Candidates whose isolating interval overlaps the target [a.lower, a.upper].
    std::vector<RealAlg> cands;
    for (const auto& r : rs.roots) if (overlaps(r)) cands.push_back(r);
    if (cands.size() == 1) return cands.front();

    // >1 (or 0) candidates: the target interval is looser than the gap between
    // distinct roots, so the coarse overlap test cannot disambiguate. REFINE each
    // candidate's isolating interval (bisection against `up`) and DROP those that
    // become provably disjoint from [a.lower, a.upper]. The true match's interval
    // always brackets its root (which lies in [a.lower,a.upper]), so it can NEVER
    // be dropped; the others converge disjoint. This is sound + complete for a
    // well-formed RealValue (interval brackets exactly one root). If the target
    // genuinely brackets two roots (malformed/loose value), the count stays >1 and
    // we fail CLOSED (exact=false → caller Unknown, never a guessed root).
    for (int round = 0; round < 80 && cands.size() != 1; ++round) {
        std::vector<RealAlg> next;
        bool progressed = false;
        for (auto& r : cands) {
            if (r.isRational()) {                 // exact point: keep iff still inside
                if (a.lower <= r.rational && r.rational <= a.upper) next.push_back(r);
                else progressed = true;
                continue;
            }
            if (algebra.refineRootInterval(r.root)) progressed = true;
            if (r.root.upper < a.lower || r.root.lower > a.upper) { progressed = true; continue; } // disjoint → drop
            next.push_back(r);
        }
        cands.swap(next);
        if (cands.empty() || !progressed) break;   // no match / cannot refine further
    }
    if (cands.size() == 1) return cands.front();

    // Ambiguous / no match: fail closed.
    exact = false;
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
    if (++nodes_ > cfg_.maxNodes) { out.status = CacStatus::Unknown; markIncomplete("node-budget"); return out; }
    // Wall-clock deadline (primary time bound): check every 256 nodes (cheap) so
    // a hard covering yields to the Collins fallback instead of grinding to the
    // global timeout. Unknown is sound (never a wrong verdict).
    if ((nodes_ & 255) == 0 && overDeadline()) { out.status = CacStatus::Unknown; markIncomplete("deadline"); return out; }

    const int n = static_cast<int>(varOrder_.size());
    const VarId var = varOrder_[level];
    const bool isLeaf = (level == n - 1);

    CacCovering cov;
    std::vector<RationalPolynomial> levelChar;   // delineators of this level's covering
    std::set<size_t> levelOrigins;               // constraint indices that delineated this covering
    long cells = 0;

    while (auto sOpt = cov.sampleUncovered()) {   // nullopt ⇒ covering gap-free
        if (++cells > cfg_.maxCellsPerLevel) { out.status = CacStatus::Unknown; markIncomplete("cell-budget"); return out; }
        bool convExact = true;
        const RealAlg s_i = toRealAlg(*algebra_, *sOpt, convExact);
        if (!convExact) { out.status = CacStatus::Unknown; markIncomplete("sample-roundtrip-ambiguous"); return out; }
        sample.push(var, s_i);

        std::vector<RationalPolynomial> cellBoundaries;
        std::vector<size_t> cellOrigins;   // constraint indices delineating THIS cell

        if (isLeaf) {
            // SPLIT the truth path from the boundary path per leaf atom
            // (characterizeLeafAtom): truth = UniformTrue / UniformFalse /
            // NonUniform, plus the exact truth at the sample and the var-boundary.
            SamplePoint prefixLeaf = sample;
            prefixLeaf.pop();                       // vars[0..level-1]
            bool allHold = true;
            bool fiberInfeasible = false;           // some atom UniformFalse on the fiber
            std::vector<RationalPolynomial> violated;
            std::vector<size_t> violatedIdx;        // parallel to `violated` (origin tracking)
            for (size_t ci = 0; ci < cons_.size(); ++ci) {
                const LeafCellResult lr = characterizeLeafAtom(
                    algebra_, kernel_, cons_[ci].poly, cons_[ci].rel, prefixLeaf, var, s_i);
                if (!lr.supported) { sample.pop(); out.status = CacStatus::Unknown; markIncomplete("leaf-atom-unsupported"); return out; }
                if (lr.truth == LeafTruth::UniformFalse) {
                    // ≡0 (or constant) and violated for ALL var ⇒ whole fiber infeasible.
                    fiberInfeasible = true; allHold = false; violated.push_back(cons_[ci].poly); violatedIdx.push_back(ci);
                } else if (!lr.holdsAtSample) {
                    // NonUniform and violated at the sample ⇒ its roots delineate.
                    allHold = false; violated.push_back(cons_[ci].poly); violatedIdx.push_back(ci);
                }
                // UniformTrue, or NonUniform-and-holds ⇒ satisfied at the sample ⇒
                // contributes nothing (no boundary, not a violation).
            }
            if (std::getenv("XOLVER_NRA_CAC_DIAG")) {
                std::ofstream st("/tmp/cac_leaf.txt", std::ios::app);
                st << "[LEAF] var=" << var << " sample=" << (s_i.isRational() ? s_i.rational.get_str() : "alg")
                   << " allHold=" << allHold << " violated=" << violated.size()
                   << " fiberInfeasible=" << fiberInfeasible << "\n";
                st.flush();
            }
            if (allHold) { satModel_ = sample; sample.pop(); out.status = CacStatus::Sat; return out; }
            if (fiberInfeasible) {
                // A leaf atom is UniformFalse on this fiber ⇒ NO value of `var`
                // satisfies it ⇒ exclude ALL of ℝ (a sound, maximal cell — never a
                // satisfied whole axis). The nullification-causing polys propagate
                // up via levelChar; characterize() projects them so the parent gets
                // the section boundary (e.g. x=1 from (x-1)y) and the covering
                // cannot cross it as if nullification held on a whole sector.
                cov.add(CacInterval::all());
                for (auto& p : violated) levelChar.push_back(std::move(p));
                levelOrigins.insert(violatedIdx.begin(), violatedIdx.end());
                sample.pop();
                continue;
            }
            cellBoundaries = std::move(violated);
            cellOrigins = std::move(violatedIdx);
        } else {
            CoverOut rec = getUnsatCover(level + 1, sample);
            if (rec.status == CacStatus::Sat)     { sample.pop(); out.status = CacStatus::Sat; return out; }
            if (rec.status == CacStatus::Unknown) { sample.pop(); out.status = CacStatus::Unknown; return out; }
            cellOrigins.assign(rec.origins.begin(), rec.origins.end());
            // rec UNSAT: project its characterization down, eliminating var_{level+1}.
            // `sample` holds vars[0..level]; the required coefficients (in those
            // vars) are evaluated against it (McCallum sample-aware projection).
            CharacterizationResult ch = characterize(rec.charPolys, varOrder_[level + 1], kernel_, &sample);
            if (!ch.complete) { sample.pop(); out.status = CacStatus::Unknown; markIncomplete("characterize-incomplete"); return out; }
            cellBoundaries = std::move(ch.downwardPolys);
        }

        // Cell on var's axis around s_i, from boundary polys isolated at the prefix.
        // Leaf-NonUniform boundaries are violated original constraints (none vanish
        // — vanishing leaf atoms were handled above as UniformFalse / UniformTrue);
        // non-leaf boundaries are characterization polys (vanishing ⇒ Lazard
        // residual recovery inside). Neither path silently skips a vanishing poly.
        SamplePoint prefix = sample;
        prefix.pop();                                   // vars[0..level-1]
        const CellResult cr = intervalFromCharacterization(algebra_, kernel_, cellBoundaries,
                                                           prefix, var, s_i);
        sample.pop();                                   // restore for next iteration
        if (!cr.supported) { out.status = CacStatus::Unknown; markIncomplete(isLeaf ? "interval-unsupported-leaf" : "interval-unsupported-nonleaf"); return out; }
        cov.add(cr.interval);
        for (auto& p : cellBoundaries) levelChar.push_back(std::move(p));
        levelOrigins.insert(cellOrigins.begin(), cellOrigins.end());
    }

    // The covering is gap-free over ℝ (loop exited) and every cell was a
    // `supported` interval from a complete characterization ⇒ sound UNSAT.
    out.status = CacStatus::Unsat;
    out.charPolys = std::move(levelChar);
    out.origins = std::move(levelOrigins);
    return out;
}

void CacEngine::markIncomplete(const char* why) {
    unsatTrustworthy_ = false;   // any incompleteness ⇒ UNSAT may NOT rest on this run
    lastUnknown_ = why;
}

bool CacEngine::overDeadline() {
    if (deadlineHit_) return true;
    if (cfg_.deadlineMillis <= 0) return false;     // unbounded (CAC-only / sole engine)
    const auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - startTime_).count();
    if (elapsed >= cfg_.deadlineMillis) { deadlineHit_ = true; return true; }
    return false;
}

CacResult CacEngine::solve() {
    CacResult res;
    if (!buildOk_ || !algebra_ || !kernel_ || varOrder_.empty()) {
        res.status = CacStatus::Unknown;
        return res;
    }
    startTime_ = std::chrono::steady_clock::now();
    SamplePoint sample;
    const CoverOut o = getUnsatCover(0, sample);
    res.status = o.status;
    if (o.status == CacStatus::Sat) { res.model = satModel_; return res; }
    if (o.status == CacStatus::Unsat) res.unsatCore.assign(o.origins.begin(), o.origins.end());
    if (o.status == CacStatus::Unsat && !unsatTrustworthy_) {
        // Gate UNSAT on the completeness ledger: markIncomplete() drops it at every
        // inconclusive step, so an uncertified UNSAT is DOWNGRADED to Unknown
        // (never emitted). UNSAT is returned only from a gap-free covering with
        // every cell `supported`, so a sound run never trips the ledger; this is a
        // belt-and-suspenders net against a control-flow regression.
        res.status = CacStatus::Unknown;
        if (lastUnknown_.empty()) lastUnknown_ = "unsat-cert-unverified";
    }
    return res;
}

#else  // !XOLVER_HAS_LIBPOLY

CacEngine::CoverOut CacEngine::getUnsatCover(int, SamplePoint&) {
    CoverOut o; o.status = CacStatus::Unknown; return o;
}
CacResult CacEngine::solve() { CacResult r; r.status = CacStatus::Unknown; return r; }

#endif

} // namespace xolver
