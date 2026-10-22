#pragma once
#include "base/RuntimeConfig.h"

#include "search/bitblast/BitBlastEncoder.h"   // BitVec, BitBlastEncoder
#include "search/bitblast/SpaceEstimator.h"
#include "algebra/poly/PolynomialKernel.h"
#include "search/nia/preprocess/NiaNormalizer.h"
#include "search/nia/core/DomainStore.h"
#include "search/nia/search/IntegerModelValidator.h"
#include "contracts/TheoryAtomTypes.h"   // TheoryConflict
#include <cstdint>
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
        // Bound each internal SAT solve's conflicts. Zero is unlimited;
        // reaching the limit leaves this width undecided and permits widening.
        satConflictBudget_ =
            config::read<config::ReadKind::Long>("XOLVER_NIA_BITBLAST_CONFLICTS", satConflictBudget_);
        // Limit the number of encoding/SAT attempts. Seven attempts preserve
        // the existing default cascade 2,4,8,16,32,64,128. The previous declared
        // default of six was never applied to the unbounded loop.
        {
            long v = config::read<config::ReadKind::Long>("XOLVER_NIA_BITBLAST_MAX_ITERS",
                                    static_cast<long>(maxIters_));
            if (v > 0 && v <= 64) maxIters_ = static_cast<unsigned>(v);
        }
        // XOLVER_NIA_BITBLAST_MAX_BITWIDTH=<W> bounds the per-variable
        // bit width (default 128). Lowering it forces the cascade to give
        // up earlier on clusters whose models exceed the cap; raising it
        // lets large bounded instances bit-blast more freely. Capped to
        // [8, 4096] to prevent encoding pathology.
        {
            long v = config::read<config::ReadKind::Long>("XOLVER_NIA_BITBLAST_MAX_BITWIDTH",
                                    static_cast<long>(maxBW_));
            if (v >= 8 && v <= 4096) maxBW_ = static_cast<unsigned>(v);
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
    unsigned maxBW_ = 128;   // Maximum width of any encoded integer variable.
    unsigned maxIters_ = 7;  // Number of attempts, including the initial width.

    // Maximum fresh SAT variables in an encoding; zero means unlimited.
    // Enforced by BitBlastEncoder, including on intermediate arithmetic gates.
    uint64_t gateBudget_ = defaultGateBudget();
    static uint64_t defaultGateBudget();

    long satConflictBudget_ = 0; // XOLVER_NIA_BITBLAST_CONFLICTS (0 = unlimited)
    // Reuse only the last definitive answer, with the complete input and its
    // reasons. Unknown is an attempt outcome, not a reusable logical answer:
    // another call may have a refreshed deadline or larger resource budget.
    // Keeping one entry also avoids retaining every historical CDCL branch.
    struct CachedResult {
        std::string key;
        BitBlastResult result;
    };
    std::optional<CachedResult> lastResult_;
    static std::string queryKey(const std::vector<NormalizedNiaConstraint>& cs,
                                const DomainStore& domains);
};

} // namespace xolver::bitblast
