#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"  // NormalizedNiaConstraint
#include "theory/arith/nia/search/IntegerModelValidator.h"  // IntegerModel, IntegerModelValidator
#include <memory>
#include <optional>
#include <vector>

namespace xolver {

class LiaSolver;            // complete-LIA decision (defined in LiaSolver.h)
class TheoryAtomRegistry;
class PolynomialKernel;

// Embedded complete-LIA decision used by NiaSolver's nia.linear-decide stage.
//
// Isolated in its own translation unit on purpose: pulling LiaSolver.h into
// NiaSolver.cpp drags in lra/GeneralSimplex.h, whose `xolver::BoundInfo`
// collides (ODR) with the identically-named struct in
// linearizer/LinearizationTypes.h that NiaSolver.cpp already includes via
// NiaLinearizationAdapter.h. Keeping the LiaSolver include here avoids the
// clash; NiaSolver only forward-declares this class.
class NiaLinearDecider {
public:
    NiaLinearDecider();
    ~NiaLinearDecider();   // out-of-line: destroys the unique_ptr<LiaSolver>

    // Replay the active trail into a complete-LIA decision procedure and return
    // an exact integer model IFF the linear system is SAT and the harvested
    // model validates against `normalized` (defense in depth). Returns nullopt
    // on UNSAT / Unknown / non-integer model — the caller then falls through to
    // the existing NIA stages, so this never produces an UNSAT verdict.
    std::optional<IntegerModel> decide(
        TheoryAtomRegistry* registry,
        PolynomialKernel& kernel,
        const std::vector<NormalizedNiaConstraint>& normalized,
        const IntegerModelValidator& validator);

private:
    std::unique_ptr<LiaSolver> lia_;   // lazily constructed on first decide()
};

}  // namespace xolver
