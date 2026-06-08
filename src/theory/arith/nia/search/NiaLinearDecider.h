#pragma once

#include "theory/arith/nia/preprocess/NiaNormalizer.h"  // NormalizedNiaConstraint
#include "theory/arith/nia/search/IntegerModelValidator.h"  // IntegerModel, IntegerModelValidator
#include "theory/core/TheoryAtomTypes.h"  // TheoryLemma, TheoryConflict
#include "sat/SatSolver.h"                 // SatVar, SatLit
#include <functional>
#include <memory>
#include <optional>
#include <unordered_set>
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

    // Decide the all-linear constraint set via a complete-LIA decision procedure.
    //
    // Returns an exact integer model IFF the system is SAT and the harvested
    // model validates against `normalized` (defense in depth).
    //
    // If the ROOT LP relaxation is infeasible (a genuine, Farkas-certified
    // infeasibility of the asserted atoms), sets *outConflict to a sound theory
    // conflict whose literals are exactly the `reason` SatLits of `normalized`
    // (the real asserted SAT literals) — the caller may return it to prune the
    // SAT search. outConflict is left untouched on SAT / Unknown / B&B-cap.
    //
    // Returns nullopt (and no conflict) when neither a model nor a root conflict
    // is found; the caller then falls through to the existing NIA stages.
    std::optional<IntegerModel> decide(
        TheoryAtomRegistry* registry,
        PolynomialKernel& kernel,
        const std::vector<NormalizedNiaConstraint>& normalized,
        const IntegerModelValidator& validator,
        std::optional<TheoryConflict>* outConflict = nullptr);

    // Standard-effort linear PROPAGATION (XOLVER_NIA_LINEAR_PROP). Builds the
    // embedded simplex from the current normalized constraint set and runs the
    // root LP only (no branch-and-bound), then:
    //   - if the LP relaxation is infeasible, sets *outConflict to the sound
    //     Farkas conflict over the real asserted reasons (caller may return it
    //     to prune the SAT search);
    //   - otherwise scans `registry` for UNASSIGNED arithmetic atoms whose
    //     variables are ALL pinned by the simplex, appending a fixed-value
    //     entailment lemma `(¬reasons ∨ atom)` for each into *outEntailments
    //     (deduped via *emittedKeys, capped at maxEmit).
    // `isAssigned(satVar)` skips atoms already decided on the trail.
    // `litIsTrue(satLit)` is the soundness firewall: an entailment is emitted
    // only when EVERY pin reason is currently true on the trail, so the lemma's
    // antecedent literals are all asserted and `(∧reasons) → atom` holds now.
    // No model is constructed; nothing is returned (results flow via out-params).
    void collectLinearProp(
        TheoryAtomRegistry* registry,
        PolynomialKernel& kernel,
        const std::vector<NormalizedNiaConstraint>& normalized,
        const std::function<bool(SatVar)>& isAssigned,
        const std::function<bool(SatLit)>& litIsTrue,
        std::optional<TheoryConflict>* outConflict,
        std::vector<TheoryLemma>* outEntailments,
        std::unordered_set<uint64_t>* emittedKeys,
        size_t maxEmit);

private:
    std::unique_ptr<LiaSolver> lia_;   // lazily constructed on first decide()
};

}  // namespace xolver
