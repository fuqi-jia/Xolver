#include "search/linearizer/LinearBoundMirror.h"
#include "search/linear/LinearConstraintRegistration.h"
#include "search/nia/search/NiaLinearizationAdapter.h"
#include "search/linearizer/DomainStoreBoundStore.h"
#include "algebra/linear/LinearExpr.h"

namespace xolver {

NiaLinearizationAdapter::NiaLinearizationAdapter(PolynomialKernel& kernel,
                                                   TheoryAtomRegistry* registry)
    : kernel_(kernel), linearizer_(kernel, registry), registry_(registry) {}

std::vector<TheoryLemma> NiaLinearizationAdapter::mirrorActiveLinearBounds(
    const std::vector<LinearizerActiveAssignment>& activeAssignments,
    TheoryId targetLinearTheory) {

    return mirrorLinearBounds(activeAssignments, SortKind::Int, kernel_, registry_, targetLinearTheory);
}

LinearizationResult NiaLinearizationAdapter::runLinearizer(
    const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
    const DomainStore& domains,
    TheoryLemmaStorage& /*lemmaDb*/,
    const LinearizationConfig& config) {

    DomainStoreBoundStore boundStore(domains);
    std::vector<LinearizationConstraint> constraints;
    constraints.reserve(nonlinearConstraints.size());
    for (const auto& c : nonlinearConstraints)
        constraints.push_back({c.poly, c.rel, c.reason});
    return linearizer_.run(constraints, boundStore, TheoryId::NIA, config);
}

void NiaLinearizationAdapter::markEmitted(const CutCacheKey& key) {
    linearizer_.markEmitted(key);
}

} // namespace xolver
