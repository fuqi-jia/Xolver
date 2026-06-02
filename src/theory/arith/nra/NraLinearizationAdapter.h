#pragma once

#include "theory/arith/linearizer/IncrementalLinearizer.h"
#include "theory/arith/linearizer/LinearizationResult.h"
#include "theory/arith/linear/LinearConstraintNormalizer.h"
#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

// Generic active assignment for mirror step
struct GenericActiveAssignment {
    SatLit lit;
    TheoryAtomRecord atom;
    bool value;
};

class NraLinearizationAdapter {
public:
    explicit NraLinearizationAdapter(PolynomialKernel& kernel,
                                     TheoryAtomRegistry* registry);

    std::vector<TheoryLemma> mirrorActiveLinearBounds(
        const std::vector<GenericActiveAssignment>& activeAssignments,
        TheoryId targetLinearTheory);

    LinearizationResult runLinearizer(
        const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
        TheoryLemmaStorage& lemmaDb);

    // NEW: same as runLinearizer but seeds BoundStore with sign-only bounds
    // derived from positivity assertions. Required to make Family 0 sign-only
    // cuts in MonomialBound/McCormick actually fire when LRA sibling has no
    // model yet (first round) and every var is sign-pinned via assertions
    // like `(< (- var) 0)`. signMap is `var-name -> +1 (positive) / -1
    // (negative)`. Vars not in the map get no bounds (same as before).
    LinearizationResult runLinearizerWithSignBounds(
        const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
        const std::unordered_map<std::string, int>& signMap,
        TheoryLemmaStorage& lemmaDb);

    // XOLVER_NRA_LINEARIZE model-driven overload: the sibling's candidate
    // relaxation model (base var name -> rational value) seeds tight point
    // bounds [v, v] for every base var, so McCormick envelopes and the square
    // tangent refine AROUND the current point (model-construction refinement)
    // rather than emitting only the bound-free nonneg cut. Sound: every cut is
    // a globally-valid linear relaxation of the nonlinear term.
    LinearizationResult runLinearizerAtModel(
        const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
        const std::unordered_map<std::string, mpq_class>& model,
        TheoryLemmaStorage& lemmaDb);

    void markEmitted(const CutCacheKey& key);

private:
    PolynomialKernel& kernel_;
    IncrementalLinearizer linearizer_;
    TheoryAtomRegistry* registry_;
};

} // namespace xolver
