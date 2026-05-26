#include "theory/arith/nra/NraLinearizationAdapter.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/linearizer/BoundStore.h"

namespace zolver {

NraLinearizationAdapter::NraLinearizationAdapter(PolynomialKernel& kernel,
                                                   TheoryAtomRegistry* registry)
    : kernel_(kernel), linearizer_(kernel, registry), registry_(registry) {}

std::vector<TheoryLemma> NraLinearizationAdapter::mirrorActiveLinearBounds(
    const std::vector<GenericActiveAssignment>& activeAssignments,
    TheoryId targetLinearTheory) {

    std::vector<TheoryLemma> lemmas;
    SortKind sort = SortKind::Real;

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

LinearizationResult NraLinearizationAdapter::runLinearizer(
    const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
    TheoryLemmaStorage& /*lemmaDb*/) {

    // NRA V1: no bound store yet; pass empty bounds
    struct EmptyBoundStore : public BoundStore {
        std::optional<BoundInfo> get(const std::string&) const override {
            return std::nullopt;
        }
    };
    EmptyBoundStore emptyBounds;
    return linearizer_.run(nonlinearConstraints, emptyBounds, TheoryId::NRA);
}

void NraLinearizationAdapter::markEmitted(const CutCacheKey& key) {
    linearizer_.markEmitted(key);
}

} // namespace zolver
