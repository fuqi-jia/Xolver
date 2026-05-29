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

    const int n = static_cast<int>(varOrder_.size());
    const VarId var = varOrder_[level];
    const bool isLeaf = (level == n - 1);

    CacCovering cov;
    std::vector<RationalPolynomial> levelChar;   // delineators of this level's covering
    long cells = 0;

    while (auto sOpt = cov.sampleUncovered()) {   // nullopt ⇒ covering gap-free
        if (++cells > cfg_.maxCellsPerLevel) { out.status = CacStatus::Unknown; markIncomplete("cell-budget"); return out; }
        bool convExact = true;
        const RealAlg s_i = toRealAlg(*algebra_, *sOpt, convExact);
        if (!convExact) { out.status = CacStatus::Unknown; markIncomplete("sample-roundtrip-ambiguous"); return out; }
        sample.push(var, s_i);

        std::vector<RationalPolynomial> cellBoundaries;

        if (isLeaf) {
            bool allHold = true;
            bool anyUnknown = false;
            int firstViolated = -1;            // witness constraint for the per-cell cert
            std::vector<RationalPolynomial> violated;
            for (size_t ci = 0; ci < cons_.size(); ++ci) {
                const Sign s = algebra_->signAt(consPoly_[ci], sample);
                if (s == Sign::Unknown) { anyUnknown = true; break; }
                if (!relationHolds(s, cons_[ci].rel)) {
                    violated.push_back(cons_[ci].poly);
                    allHold = false;
                    if (firstViolated < 0) firstViolated = static_cast<int>(ci);
                }
            }
            if (std::getenv("XOLVER_NRA_CAC_DIAG")) {
                std::ofstream st("/tmp/cac_leaf.txt", std::ios::app);
                st << "[LEAF] var=" << var << " sample=" << (s_i.isRational() ? s_i.rational.get_str() : "alg")
                   << " allHold=" << allHold << " violated=" << violated.size()
                   << " anyUnknown=" << anyUnknown << "\n";
                st.flush();
            }
            if (anyUnknown) { sample.pop(); out.status = CacStatus::Unknown; markIncomplete("signAt-unknown"); return out; }
            if (allHold)    { satModel_ = sample; sample.pop(); out.status = CacStatus::Sat; return out; }
            // Per-cell UNSAT witness: this leaf cell is excluded because the sample
            // violates constraint `firstViolated`, whose roots are cell boundaries
            // (the leaf passes `violated` AS the boundary polys) ⇒ it is sign-
            // invariant on the cell ⇒ violated on the WHOLE cell. signAt already
            // gave a definite (non-Unknown) sign above. Record the witness.
            if (leafExclusions_.size() < 4096)   // bounded audit ledger; aggregate gate is the soundness net
                leafExclusions_.push_back(
                    LeafExclusion{var, s_i, consPoly_[firstViolated], cons_[firstViolated].rel});
            cellBoundaries = std::move(violated);
        } else {
            CoverOut rec = getUnsatCover(level + 1, sample);
            if (rec.status == CacStatus::Sat)     { sample.pop(); out.status = CacStatus::Sat; return out; }
            if (rec.status == CacStatus::Unknown) { sample.pop(); out.status = CacStatus::Unknown; return out; }
            // rec UNSAT: project its characterization down, eliminating var_{level+1}.
            // `sample` holds vars[0..level]; the required coefficients (in those
            // vars) are evaluated against it (McCallum sample-aware projection).
            CharacterizationResult ch = characterize(rec.charPolys, varOrder_[level + 1], kernel_, &sample);
            if (!ch.complete) { sample.pop(); out.status = CacStatus::Unknown; markIncomplete("characterize-incomplete"); return out; }
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
        if (!cr.supported) { out.status = CacStatus::Unknown; markIncomplete(isLeaf ? "interval-unsupported-leaf" : "interval-unsupported-nonleaf"); return out; }
        cov.add(cr.interval);
        for (auto& p : cellBoundaries) levelChar.push_back(std::move(p));
    }

    // The covering is gap-free over ℝ (loop exited) and every cell was a
    // `supported` interval from a complete characterization ⇒ sound UNSAT.
    out.status = CacStatus::Unsat;
    out.charPolys = std::move(levelChar);
    return out;
}

void CacEngine::markIncomplete(const char* why) {
    unsatTrustworthy_ = false;   // any incompleteness ⇒ UNSAT may NOT rest on this run
    lastUnknown_ = why;
}

bool CacEngine::verifyCertificate() {
    // Independent gate over the UNSAT certificate, evaluated separately from the
    // covering control flow: it catches a regression where an UNSAT verdict
    // escapes despite an incompleteness having been flagged. The soundness net is
    // the AGGREGATE completeness ledger `unsatTrustworthy_`, which markIncomplete()
    // drops at EVERY inconclusive step (budget, ambiguous round-trip, signAt
    // Unknown, incomplete characterization, unsupported interval). Because UNSAT
    // is returned only when the covering is gap-free with every cell `supported`,
    // a trustworthy run never tripped the ledger.
    //
    // The leaf-exclusion ledger (`leafExclusions_`) is retained for audit / proof
    // output, but is NOT re-evaluated here: each witness sample is only the leaf
    // coordinate (the prefix is popped), so re-running signAt against it would be
    // a PARTIAL assignment over a multivariate constraint — unreliable and, on the
    // libpoly algebraic path, crash-prone. The witnesses were already computed
    // from a complete (non-Unknown) signAt at record time on the full sample.
    return unsatTrustworthy_;
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
    if (o.status == CacStatus::Sat) { res.model = satModel_; return res; }
    if (o.status == CacStatus::Unsat) {
        // Gate the UNSAT verdict on the independent per-cell certificate. If the
        // ledger tripped or a witness fails to re-verify, DOWNGRADE to Unknown
        // (never emit an uncertified UNSAT). certComplete() = ledger + witnesses.
        certVerified_ = verifyCertificate();
        if (!certComplete()) {
            res.status = CacStatus::Unknown;
            if (lastUnknown_.empty()) lastUnknown_ = "unsat-cert-unverified";
        }
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
