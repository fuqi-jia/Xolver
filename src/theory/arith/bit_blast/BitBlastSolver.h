#pragma once

#include "theory/arith/bit_blast/BitBlastEncoder.h"   // BitVec, BitBlastEncoder
#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/core/TheoryAtomTypes.h"   // TheoryConflict
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver::bitblast {

struct BitBlastResult {
    enum class Status { Sat, UnsatComplete, Unknown };
    Status status = Status::Unknown;
    IntegerModel model;                       // valid iff Sat
    std::optional<TheoryConflict> conflict;   // valid iff UnsatComplete
};

// Orchestrates one bit-blast attempt: size widths, encode over an independent
// CaDiCaL, solve, validate SAT, and refine widths in heuristic mode. Sound by
// construction: SAT validated, UNSAT only when complete.
//
// SELF-CONTAINED SOUNDNESS: the solver encodes BOTH (a) every constraint in
// `cs` AND (b) the DomainStore hard bounds of each variable, so the SAT search
// space EQUALS the box [lb,ub]^n intersected with `cs` — it does not rely on
// `cs` happening to contain the bound atoms. A SAT model is accepted only if it
// passes IntegerModelValidator over `cs` AND lies inside the DomainStore box
// (`modelInDomains`). UNSAT is emitted only when `boxIsComplete`, with a
// conflict over the reasons of BOTH the cs constraints and the domain bounds.
class BitBlastSolver {
public:
    explicit BitBlastSolver(PolynomialKernel& kernel)
        : kernel_(kernel), estimator_(kernel) {
        if (const char* e = std::getenv("XOLVER_NIA_BITBLAST_FAST"); e && *e && *e != '0')
            fastMode_ = true;
        // XOLVER_NIA_BITBLAST_NOPRE (default-OFF): disable CaDiCaL's expensive
        // gate-extraction / equivalence-finding preprocessing in the bit-blast's
        // internal SAT solve. Profiling QF_UFNIA floored cases showed 100% of
        // CPU in CaDiCaL::Closure::find_equivalences (the gate-extraction pass)
        // inside `nia.bit-blast` — a single internal solve burning the whole
        // budget. Sound: bit-blast is candidate-only (every SAT result is
        // re-validated by IntegerModelValidator per invariant 1) and the SAT
        // verdict itself is not affected by preprocessing — only its speed.
        if (const char* e = std::getenv("XOLVER_NIA_BITBLAST_NOPRE"); e && *e && *e != '0')
            noPreprocess_ = true;
        // XOLVER_NIA_BITBLAST_CONFLICTS=<N> (default-0=unlimited): cap CaDiCaL's
        // conflict budget on the bit-blast's INTERNAL SAT solve. With NOPRE off,
        // the bottleneck on QF_UFNIA floored cases moves to CDCL propagate/search;
        // with no budget, a single internal solve burns the whole NIA stage
        // budget. The bit-blast is candidate-only (invariant 1) — a SAT-Unknown
        // result just falls through to the next NIA stage / wider bit-width.
        if (const char* e = std::getenv("XOLVER_NIA_BITBLAST_CONFLICTS"); e && *e) {
            satConflictBudget_ = std::atoll(e);
        }
    }

    BitBlastResult solve(const std::vector<NormalizedNiaConstraint>& cs,
                         const DomainStore& domains,
                         const IntegerModelValidator& validator);

    void setMaxBitWidth(unsigned w) { maxBW_ = w; }
    void setMaxIterations(unsigned n) { maxIters_ = n; }
    void setGateBudget(uint64_t b) { gateBudget_ = b; }

private:
    bool applicable(const std::vector<NormalizedNiaConstraint>& cs) const;

    // One encode+solve+validate attempt at a fixed width plan. Sat carries a
    // validated in-box model; Unsat is box-dependent (caller decides global
    // completeness); Overflow = encoding exceeded the var budget.
    struct Attempt {
        enum Kind { Sat, Unsat, Unknown, Overflow } kind = Unknown;
        IntegerModel model;
    };
    Attempt attemptAtWidths(const BitWidthPlan& plan,
                            const std::vector<NormalizedNiaConstraint>& cs,
                            const DomainStore& domains,
                            const IntegerModelValidator& validator);

    // Encode `x >= lb` and `x <= ub` (and finite-set / exclusions) for every
    // bounded variable, so the SAT search is confined to the DomainStore box.
    void encodeDomainBounds(BitBlastEncoder& enc,
                            const std::unordered_map<std::string, BitVec>& varBits,
                            const DomainStore& domains);

    // Independent check that a candidate model lies inside the DomainStore box
    // (bounds, finite sets, exclusions). Belt-and-suspenders with the encoding.
    static bool modelInDomains(const IntegerModel& model, const DomainStore& domains);

    // Conflict = negated reasons of EVERY encoded justification: all cs
    // constraints AND all domain bounds (the box participates in the UNSAT).
    // Returns nullopt if no usable reason literal exists, or if the clause is
    // self-contradictory.
    std::optional<TheoryConflict> buildCompleteConflict(
        const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains) const;

    PolynomialKernel& kernel_;
    SpaceEstimator estimator_;
    unsigned maxBW_ = 128;     // bit-width ceiling U: BLAN's paper default is 32,
                               // competition runs use >=128 to cover large
                               // solutions. 256 (the prior value) over-widens and,
                               // combined with high-degree products, blows up the
                               // SAT encoding. With the BLAN-faithful multiplier
                               // (varmin partials + constant folding) 128 is safe.
    unsigned maxIters_ = 6;    // x4 width growth per iter reaches wide widths fast (capped at maxBW_)

    // Resource cap: refuse to bit-blast when the estimated SAT-encoding cost
    // (~gate / fresh-var count, SpaceEstimator::estimateGateCost) exceeds this.
    // High-degree QF_NIA (e.g. degree-5 monomials over dozens of vars) blows the
    // encoding past available memory and aborts inside CaDiCaL with bad_alloc;
    // bailing to Unknown here is sound (other NIA stages still run) and turns an
    // OOM crash into a clean Unknown. Env-tunable via XOLVER_NIA_BITBLAST_GATE_BUDGET.
    uint64_t gateBudget_ = defaultGateBudget();
    static uint64_t defaultGateBudget();

    // XOLVER_NIA_BITBLAST_FAST (default-OFF): memoize solve() by a fingerprint of
    // (cs polys+rels, per-var domain bounds). The Full-effort bit-blast stage is
    // re-invoked across CDCL(T) theory checks with an unchanged constraint set;
    // profiling shows the SAME problem re-encoded+re-solved many times (e.g. an
    // always-overflow AProVE case attempted ~10x). The cache collapses those
    // redundant solves, freeing the time budget for the deciding width / other
    // stages. Verdict-preserving: identical input -> identical cached output.
    bool fastMode_ = false;
    bool noPreprocess_ = false;  // XOLVER_NIA_BITBLAST_NOPRE
    long satConflictBudget_ = 0; // XOLVER_NIA_BITBLAST_CONFLICTS (0 = unlimited)
    std::unordered_map<std::string, BitBlastResult> resultCache_;
    std::string fingerprint(const std::vector<NormalizedNiaConstraint>& cs,
                            const DomainStore& domains) const;
};

} // namespace xolver::bitblast
