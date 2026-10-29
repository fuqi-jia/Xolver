#pragma once

#include "search/nia/preprocess/NiaNormalizer.h"  // NormalizedNiaConstraint
#include "search/nia/search/IntegerModelValidator.h"  // IntegerModel, IntegerModelValidator
#include "contracts/TheoryAtomTypes.h"  // TheoryLemma, TheoryConflict
#include "contracts/SatSolver.h"                 // SatVar, SatLit
#include <functional>
#include <memory>
#include <optional>
#include <unordered_set>
#include <vector>

namespace xolver {

class LiaSolver;            // bounded integer-model search (defined in LiaSolver.h)
class TheoryAtomRegistry;
class PolynomialKernel;

// Embedded bounded integer-model search used by NiaSolver's nia.linear-decide stage.
//
// Kept in its own translation unit to keep the simplex implementation out of
// NiaSolver headers and limit compilation dependencies.
class NiaLinearDecider {
public:
    NiaLinearDecider();
    ~NiaLinearDecider();   // out-of-line: destroys the unique_ptr<LiaSolver>

    // Search the all-linear constraint set with a bounded integer-model procedure.
    //
    // Returns an exact integer model only after it validates against `normalized`.
    // A satisfiable system may exceed the search budget and return no model.
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

private:
    std::unique_ptr<LiaSolver> lia_;   // lazily constructed on first decide()
};

}  // namespace xolver
