#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/cac/Covering.h"
#include "theory/arith/nra/core/CdcacValue.h"   // SamplePoint, RealAlg
#include "expr/types.h"

#include <string>
#include <vector>

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
};

class CacEngine {
public:
    struct Config {
        long maxCellsPerLevel = 4000;   // covering blow-up guard (⇒ Unknown)
        long maxNodes = 400000;         // total recursion-node budget (⇒ Unknown)
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

    // ---- Per-cell UNSAT certificate (the oracle-blind soundness gate) --------
    // The CacEngine's UNSAT rests on: every cell built from a COMPLETE
    // characterization + a `supported` interval, and every covering gap-free.
    // The control flow already returns Unknown on any incompleteness; this is an
    // INDEPENDENT, auditable ledger that re-confirms it. `solve()` trusts an
    // UNSAT verdict only when `certComplete()` holds — a belt-and-suspenders gate
    // that catches a control-flow regression where UNSAT could escape despite an
    // incomplete cell. Each excluded LEAF cell also records the constraint that
    // witnesses its infeasibility (the exclusion is sound only if that constraint
    // is actually violated at the cell sample — re-verified before trusting).
    struct LeafExclusion {
        VarId var = NullVar;
        RealAlg sample;
        PolyId violatedPoly = NullPoly;   // a constraint violated at `sample`
        Relation rel = Relation::Eq;
    };
    bool certComplete() const { return unsatTrustworthy_ && certVerified_; }
    const std::vector<LeafExclusion>& leafExclusions() const { return leafExclusions_; }

private:
    struct CoverOut {
        CacStatus status = CacStatus::Unknown;
        std::vector<RationalPolynomial> charPolys;   // delineate this level's covering
    };
    CoverOut getUnsatCover(int level, SamplePoint& sample);

    LibpolyBackend* algebra_;
    PolynomialKernel* kernel_;
    std::vector<VarId> varOrder_;
    std::vector<CacConstraint> cons_;
    std::vector<PolyId> consPoly_;   // toPrimitiveInteger(poly) per constraint
    bool buildOk_ = true;            // false ⇒ a constraint was not representable
    SamplePoint satModel_;           // captured at the SAT leaf
    Config cfg_;
    long nodes_ = 0;
    std::string lastUnknown_;        // bail reason (diagnostics)
    long maxDepth_ = 0;              // deepest level reached

    // Per-cell UNSAT certificate state (see public accessors above).
    bool unsatTrustworthy_ = true;   // ANDed false at every incompleteness point
    bool certVerified_ = false;      // set by an independent post-pass on UNSAT
    std::vector<LeafExclusion> leafExclusions_;   // witness per excluded leaf cell
    void markIncomplete(const char* why);         // unsatTrustworthy_=false + lastUnknown_
    bool verifyCertificate();                     // independent re-check before trusting UNSAT
};

} // namespace xolver
