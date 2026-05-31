#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/cac/Covering.h"
#include "theory/arith/nra/core/CdcacValue.h"   // SamplePoint, RealAlg
#include "expr/types.h"

#include <string>
#include <vector>
#include <chrono>
#include <set>

namespace xolver {

class PolynomialKernel;
class LibpolyBackend;

// ============================================================================
// CAC engine (lever 3, module C — see ../CAC.md). Conflict-driven cylindrical
// algebraic coverings (Ábrahám-Davenport-England-Kremer 2021): NO full Collins
// closure — projection is sample-driven and single-cell, so projected polys
// stay small (the fix for the doubly-exponential `buildClosure` that times out
// on Sturm-MBO).
//
//   get_unsat_cover(i, s):                       # s assigns varOrder[0..i-1]
//     while x_i = covering.sampleUncovered():
//       s' = s ∪ {x_i}
//       if i == last: if all constraints hold at s' -> SAT(s');
//                     else exclude the cell delineated by the violated polys.
//       else:         (sat?, O) = get_unsat_cover(i+1, s'); if sat -> SAT;
//                     else exclude the cell from characterize(O) projected to x_i.
//     # covering gap-free  -> UNSAT at this level (return its characterization up)
//
// SOUNDNESS (CAC UNSAT has NO model-validation backstop):
//   * SAT  ⇐ a full sample on which EVERY constraint's exact sign satisfies its
//            relation (signAt; an Unknown sign ⇒ engine Unknown).
//   * UNSAT ⇐ the top-level covering is gap-free (CacCovering::isComplete) AND
//            every cell was built from a COMPLETE characterize + a `supported`
//            interval. ANY incomplete/inconclusive step (characterize
//            incomplete, interval unsupported, sign Unknown, budget) ⇒ Unknown,
//            never UNSAT. The characterization is CONSERVATIVE (it may carry
//            extra polynomials): extra boundaries only refine cells — they never
//            cause a false UNSAT.
//
// Requires libpoly; the stub `solve()` returns Unknown without it.
// ============================================================================

struct CacConstraint {
    RationalPolynomial poly;   // constraint is  poly  rel  0
    Relation rel;
};

enum class CacStatus { Sat, Unsat, Unknown };

struct CacResult {
    CacStatus status = CacStatus::Unknown;
    SamplePoint model;   // a full assignment, valid iff status == Sat
    // UNSAT core: indices (into the constructor's constraint vector) of the
    // constraints that actually DELINEATED the gap-free covering — i.e. the
    // ones whose violation/boundary produced an excluded cell. A conservative
    // SUPERSET of a truly-minimal core (the union projection can't attribute
    // per-cell), but strictly smaller than "all constraints" in general, so the
    // combination/conflict layer can (a) minimize the learned lemma and (b)
    // include exactly the interface-(dis)eq lits that participated. Valid iff
    // status == Unsat; EMPTY means "could not attribute" ⇒ caller falls back to
    // the full constraint set (sound).
    std::vector<size_t> unsatCore;
    // #63 Phase C2 follow-on: when status == Unknown and the failure came from
    // `characterizeLeafAtom → signAt == Unknown` on an algebraic-prefix sample,
    // expose the failing partial assignment so the caller (NraSolver) can retry
    // with rational midpoints for the algebraic coords. Empty otherwise.
    // Soundness: the rational retry is a candidate generator only — any SAT it
    // produces must be model-validated against original constraints by the
    // caller (invariant 1).
    SamplePoint unknownSample;
};

class CacEngine {
public:
    struct Config {
        // Runaway/OOM guards (⇒ Unknown when hit — sound: a hit cap is never a
        // wrong answer). Sized to the COMPETITION budget (1200s/30GB), NOT a
        // dev-conservative throttle: at ~tens of ms/cell the 1200s wall-clock
        // binds long before these, and the cell/node structures stay well under
        // 30GB. (The old 4000/400000 could bail a hard covering in ~minutes,
        // throttling CAC before its real time budget.)
        long maxCellsPerLevel = 200000;     // per-level covering blow-up guard
        long maxNodes = 20000000;           // total recursion-node budget (memory guard)
        // Wall-clock deadline for the covering search (ms; 0 = unbounded). This is
        // the PRIMARY time bound — the node/cell caps are just memory guards. In
        // the HYBRID (Collins fallback present) CAC gets a bounded time-share so a
        // hard covering yields to Collins (Unknown→fallback) instead of grinding
        // to the global timeout and starving it. When CAC is the SOLE engine
        // (no Collins), leave it 0 (unbounded) and rely on the external timeout.
        long deadlineMillis = 0;
        // Track 1 #39: early-infeasibility probe at every non-leaf sample.
        // signAt every constraint whose mainLevel ≤ current level; a definite-
        // nonzero violating sign ⇒ exclude the cell on var WITHOUT recursing.
        // signAt = Zero (nullification) routes via the existing characterize
        // path (NOT a direct conflict). Default OFF; NraSolver stageCac flips
        // it from XOLVER_NRA_CAC_EARLY_INFEAS.
        bool earlyInfeas = false;
        // Track 2 #40: prune subsumed cells before flattening to charPolys/
        // origins (cvc5 cleanIntervals analog). Sound: the surviving cells
        // still cover ℝ (a subsumed cell's interval is contained in the
        // subsuming one, so removing it leaves the union unchanged); only
        // PROPAGATION is trimmed — smaller projection input at the parent,
        // tighter (still sound) unsatCore. Default OFF; NraSolver stageCac
        // flips it from XOLVER_NRA_CAC_PRUNE_INTERVALS.
        bool pruneIntervals = false;
        // #48 fix toggle: inject equations with mainLevel > level into
        // levelChar when EARLY_INFEAS fired anywhere at this level. Soundness
        // fix for the false-UNSAT on equation-heavy cases (e.g. Geogebra
        // IsoRightTriangle) when CAC has enough wall to complete its covering
        // (ALL_EFFORTS / CAC_ONLY). Default OFF — the empty-downward gate
        // alone catches the projection-collapse case; this extra injection
        // helps the algebraic-resultant-chain case but costs measurable perf
        // (broad-714 was -10 decisions). Flip ON via
        // XOLVER_NRA_CAC_EARLY_INFEAS_SAFE for extended-wall configs.
        bool earlyInfeasSafe = false;
        // Track C round 2 (#49): in-loop interval pruning. Extends #40's
        // post-loop subsumption prune by checking each newly added cell vs
        // existing cells INSIDE the while loop. Subsumed cells are dropped
        // from cellsList immediately so it stays minimal during the loop —
        // smaller levelChar at flatten, smaller parent Lazard projection
        // input. cov stays consistent (merged() unions all intervals;
        // dropping subsumed entries doesn't affect coverage). Default OFF;
        // NraSolver flips it from XOLVER_NRA_CAC_INLOOP_PRUNE.
        bool inloopPrune = false;
    };

    CacEngine(LibpolyBackend* algebra, PolynomialKernel* kernel,
              std::vector<VarId> varOrder, std::vector<CacConstraint> constraints,
              Config cfg);
    CacEngine(LibpolyBackend* algebra, PolynomialKernel* kernel,
              std::vector<VarId> varOrder, std::vector<CacConstraint> constraints);

    CacResult solve();

    // Why solve() returned Unknown (for diagnostics / lever triage). Empty if
    // it did not return Unknown.
    const std::string& lastUnknown() const { return lastUnknown_; }
    long maxDepthReached() const { return maxDepth_; }

    // ---- UNSAT completeness certificate (the oracle-blind soundness gate) -----
    // The CacEngine's UNSAT rests on a gap-free covering with every cell built
    // from a COMPLETE characterization + a `supported` interval. markIncomplete()
    // drops `unsatTrustworthy_` at EVERY inconclusive step, so solve() trusts an
    // UNSAT verdict only when this aggregate ledger held — a belt-and-suspenders
    // gate that downgrades an uncertified UNSAT to Unknown (never emits it).
    bool unsatCertified() const { return unsatTrustworthy_; }

private:
    struct CoverOut {
        CacStatus status = CacStatus::Unknown;
        std::vector<RationalPolynomial> charPolys;   // delineate this level's covering
        // Constraint indices (into cons_) that contributed to THIS level's UNSAT
        // covering: at the leaf, every violated atom; at a non-leaf, the union of
        // the child recursions' origins. Propagated up to form CacResult::unsatCore.
        std::set<size_t> origins;
        // #63 Phase C2 follow-on: failing partial sample carried up the recursion
        // when status == Unknown originated from `leaf-atom-unsupported`. Populated
        // at the leaf failure site BEFORE sample.pop(), then propagated unchanged
        // through parent CoverOuts so solve() can hand it to NraSolver for the
        // rational-fallback retry. Empty if the Unknown came from a different
        // failure mode (interval-unsupported, characterize-incomplete, etc.).
        SamplePoint unknownSample;
    };
    CoverOut getUnsatCover(int level, SamplePoint& sample);

    LibpolyBackend* algebra_;
    PolynomialKernel* kernel_;
    std::vector<VarId> varOrder_;
    std::vector<CacConstraint> cons_;
    // Per-constraint cache, parallel to cons_ (populated in the constructor):
    //   consMainLevel_[ci] = highest level in varOrder_ that appears in cons_[ci].poly,
    //                        or -1 if the poly is constant.  Used by the early-
    //                        infeasibility probe to filter constraints whose sign
    //                        is fully decidable at the current prefix (mvLevel<=level).
    //   consPid_[ci]       = libpoly PolyId for signAt (one-time toPrimitiveInteger),
    //                        avoiding per-probe re-normalization.
    std::vector<int> consMainLevel_;
    std::vector<PolyId> consPid_;
    bool buildOk_ = true;            // false ⇒ a constraint was not representable
    bool earlyInfeas_ = false;       // XOLVER_NRA_CAC_EARLY_INFEAS gate, cached at construction
    bool pruneIntervals_ = false;    // XOLVER_NRA_CAC_PRUNE_INTERVALS gate
    bool earlyInfeasSafe_ = false;   // XOLVER_NRA_CAC_EARLY_INFEAS_SAFE gate (#48 injection)
    bool inloopPrune_ = false;       // XOLVER_NRA_CAC_INLOOP_PRUNE gate (#49)
    SamplePoint satModel_;           // captured at the SAT leaf
    Config cfg_;
    long nodes_ = 0;
    std::string lastUnknown_;        // bail reason (diagnostics)
    long maxDepth_ = 0;              // deepest level reached

    // UNSAT completeness certificate (see accessor above).
    bool unsatTrustworthy_ = true;          // ANDed false at every incompleteness point
    void markIncomplete(const char* why);   // unsatTrustworthy_=false + lastUnknown_

    // Wall-clock deadline (cfg_.deadlineMillis). Set at solve() start; checked
    // periodically in getUnsatCover. Returns true once the budget is exhausted.
    std::chrono::steady_clock::time_point startTime_;
    bool deadlineHit_ = false;
    bool overDeadline();
};

} // namespace xolver
