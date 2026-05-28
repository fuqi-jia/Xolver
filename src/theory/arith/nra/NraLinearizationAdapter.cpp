#include "theory/arith/nra/NraLinearizationAdapter.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/linearizer/BoundStore.h"

namespace xolver {

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

LinearizationResult NraLinearizationAdapter::runLinearizerAtModel(
    const std::vector<NormalizedNiaConstraint>& nonlinearConstraints,
    const std::unordered_map<std::string, mpq_class>& model,
    TheoryLemmaStorage& /*lemmaDb*/) {

    // Point bounds: every base var present in the candidate model gets a tight
    // [v, v] interval so the envelope/secant/tangent cuts have finite bounds to
    // work with and refine AROUND the current candidate point. These cuts are
    // globally-valid relaxations of the nonlinear term (sound regardless of the
    // chosen point); the SAT model is still exact-validated before SAT.
    struct ModelBoundStore : public BoundStore {
        const std::unordered_map<std::string, mpq_class>& m;
        explicit ModelBoundStore(const std::unordered_map<std::string, mpq_class>& mm) : m(mm) {}
        std::optional<BoundInfo> get(const std::string& v) const override {
            auto it = m.find(v);
            if (it == m.end()) return std::nullopt;
            BoundInfo bi;
            bi.lower = it->second;
            bi.upper = it->second;
            bi.hasLower = true;
            bi.hasUpper = true;
            // No reasons: these are model-construction points, not asserted
            // bounds. The cut lemma still carries the nonlinear-constraint
            // reason, so it remains sound (a global relaxation).
            bi.lowerReasonComplete = true;
            bi.upperReasonComplete = true;
            return bi;
        }
    };
    ModelBoundStore bounds(model);
    LinearizationConfig cfg;
    cfg.emitAllMcCormick = true;
    cfg.emitSquareNonneg = true;
    cfg.emitSquareTangent = true;
    cfg.emitSquareSecant = true;
    cfg.maxLemmas = 16;
    cfg.maxCutsPerTerm = 4;
    return linearizer_.run(nonlinearConstraints, bounds, TheoryId::NRA, cfg, &model);
}

void NraLinearizationAdapter::markEmitted(const CutCacheKey& key) {
    linearizer_.markEmitted(key);
}

} // namespace xolver
