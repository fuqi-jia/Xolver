#include "theory/arith/nia/search/NiaLinearizationAdapter.h"
#include "theory/arith/linearizer/DomainStoreBoundStore.h"
#include "theory/arith/linear/LinearExpr.h"

namespace nlcolver {

NiaLinearizationAdapter::NiaLinearizationAdapter(PolynomialKernel& kernel,
                                                   TheoryAtomRegistry* registry)
    : kernel_(kernel), linearizer_(kernel, registry), registry_(registry) {}

std::vector<TheoryLemma> NiaLinearizationAdapter::mirrorActiveLinearBounds(
    const std::vector<LinearizerActiveAssignment>& activeAssignments,
    TheoryId targetLinearTheory) {

    std::vector<TheoryLemma> lemmas;
    SortKind sort = SortKind::Int;

    for (const auto& a : activeAssignments) {
        std::optional<ZeroLinearConstraint> zOpt;

        if (auto* payload = std::get_if<LinearAtomPayload>(&a.atom.payload)) {
            zOpt = LinearConstraintNormalizer::makeEffectiveConstraint(*payload, a.value, sort);
        } else if (auto* payload = std::get_if<PolynomialAtomPayload>(&a.atom.payload)) {
            zOpt = LinearConstraintNormalizer::makeEffectiveConstraint(*payload, a.value, sort, kernel_);
        }

        if (!zOpt) continue;

        SatLit mirrorLit = LinearConstraintNormalizer::registerLinearConstraint(
            *registry_, *zOpt, targetLinearTheory);

        if (mirrorLit.var != 0) {
            lemmas.push_back(TheoryLemma{{a.lit.negated(), mirrorLit}});
        }
    }

    return lemmas;
}

LinearizationResult NiaLinearizationAdapter::runLinearizer(
    const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
    const DomainStore& domains,
    TheoryLemmaStorage& /*lemmaDb*/,
    const LinearizationConfig& config) {

    DomainStoreBoundStore boundStore(domains);
    return linearizer_.run(nonlinearConstraints, boundStore, TheoryId::NIA, config);
}

void NiaLinearizationAdapter::markEmitted(const CutCacheKey& key) {
    linearizer_.markEmitted(key);
}

} // namespace nlcolver
