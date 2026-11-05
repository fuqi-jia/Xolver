#pragma once

#include "search/nra/reasoners/NlaCutGenerator.h"
#include "search/refute/SignDefinitenessRefuter.h"
#include "algebra/poly/PolynomialKernel.h"

#include <vector>
#include <map>

namespace xolver {
namespace nla {

// Convert solver intervals into a batch of NLA cuts. Callers own scheduling
// and supply explained bounds; the generator has no runtime switches.
//
// Soundness role: the runner adds no new soundness assumptions; it only
// composes existing generator methods. Every returned cut carries the
// soundness invariant from its source generator method, and the caller
// is free to filter / pick top-k without losing soundness.
class NlaCutsRunner {
public:
    explicit NlaCutsRunner(PolynomialKernel& kernel);

    // Extract rational bounds from the current signed polynomial context.
    // Each endpoint retains its strongest source; the interval explanation
    // includes both endpoints. Weaken strict endpoints without rounding.
    std::vector<VarInterval> collectIntervals(
        const std::vector<SignRefuteConstraint>& constraints);

    // Generate the union of cuts available from the listed intervals.
    // For each interval: monotonicitySquare(x). For each pair: both
    // monotonicityProduct and mccormickBilinear. Tangent cuts require a
    // model point, so the caller passes them separately via runTangents.
    //
    // The caller is expected to budget — emitting all pairwise cuts is
    // O(n^2); for now we cap at the first `maxPairs` pairs to keep cost
    // bounded. `maxPairs = 0` means "no pair cuts".
    std::vector<NlaCut> runShapeCuts(const std::vector<VarInterval>& vars,
                                     std::size_t maxPairs = 16);

    // Tangent cuts at a list of (varPoly, modelPoint) pairs. Useful when
    // the caller has a current model and wants tangent linearisations of
    // each quadratic monomial at its model value. Reasons may be empty if
    // the tangent's correctness is unconditional (any model point gives
    // the sound cut (x-m)^2 >= 0 regardless of how m was picked).
    std::vector<NlaCut> runTangents(
            const std::vector<std::pair<PolyId, mpq_class>>& points,
            const std::vector<SatLit>& reasons);

private:
    PolynomialKernel& kernel_;
    NlaCutGenerator gen_;
    using PolynomialShape = std::vector<std::pair<MonomialKey, mpq_class>>;
    // Only mathematical identities persist. Bound explanations are recomputed
    // for every call, including after a source changes or is withdrawn.
    std::map<PolynomialShape, PolyId> polynomials_;
    void sharePolynomials(std::vector<NlaCut>& cuts);
};

} // namespace nla
} // namespace xolver
