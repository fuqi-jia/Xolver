#pragma once

#include "theory/arith/bit_blast/BitBlastEncoder.h"   // BitVec, BitBlastEncoder
#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"
#include "theory/core/TheoryAtomTypes.h"   // TheoryConflict
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace zolver::bitblast {

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
        : kernel_(kernel), estimator_(kernel) {}

    BitBlastResult solve(const std::vector<NormalizedNiaConstraint>& cs,
                         const DomainStore& domains,
                         const IntegerModelValidator& validator);

    void setMaxBitWidth(unsigned w) { maxBW_ = w; }
    void setMaxIterations(unsigned n) { maxIters_ = n; }

private:
    bool applicable(const std::vector<NormalizedNiaConstraint>& cs) const;

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
    unsigned maxBW_ = 256;     // QF_NIA: large solutions need headroom
    unsigned maxIters_ = 6;    // with doubling growth, reaches up to maxBW_
};

} // namespace zolver::bitblast
