#include "theory/arith/icp/ContractorFactoryQ.h"
#include "theory/arith/icp/contractors/RelationContractorQ.h"
#include "theory/arith/icp/contractors/MonomialMultivariateContractorQ.h"
#include "theory/arith/icp/contractors/MixedQuadraticContractorQ.h"
#include "theory/arith/icp/contractors/BilinearContractorQ.h"

namespace xolver {

ContractorFactoryQ::BuildResult ContractorFactoryQ::build(
    const std::vector<IcpConstraint>& constraints,
    PolynomialKernel& kernel) {

    BuildResult result;
    size_t id = 0;

    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        auto vars = kernel.variables(c.poly);

        if (vars.size() == 1) {
            // Univariate: V1/V2/V3 inside RelationContractorQ.
            auto contractor = std::make_unique<RelationContractorQ>(c, kernel);
            for (const auto& v : contractor->vars()) {
                result.watchers.addWatcher(v, id);
            }
            result.contractors.push_back(std::move(contractor));
            ++id;
        } else if (vars.size() >= 2) {
            // Multivariate: try the available shape contractors per
            // candidate live var. Each contractor self-checks via
            // isUsable() and the shapes are mutually exclusive by
            // construction (V4 = pure live^d + rest with NO live^1
            // mixed terms; V5b = quadratic with at least one live^1
            // term). A polynomial may match V4 on one live var and V5b
            // on another — both register.
            for (const auto& liveVar : vars) {
                auto v4 = std::make_unique<MonomialMultivariateContractorQ>(
                    c, kernel, liveVar);
                if (v4->isUsable()) {
                    for (const auto& w : v4->vars()) {
                        result.watchers.addWatcher(w, id);
                    }
                    result.contractors.push_back(std::move(v4));
                    ++id;
                    continue;  // mutually exclusive with V5b/V5c
                }
                auto v5b = std::make_unique<MixedQuadraticContractorQ>(
                    c, kernel, liveVar);
                if (v5b->isUsable()) {
                    for (const auto& w : v5b->vars()) {
                        result.watchers.addWatcher(w, id);
                    }
                    result.contractors.push_back(std::move(v5b));
                    ++id;
                    continue;
                }
                auto v5c = std::make_unique<BilinearContractorQ>(
                    c, kernel, liveVar);
                if (!v5c->isUsable()) continue;
                for (const auto& w : v5c->vars()) {
                    result.watchers.addWatcher(w, id);
                }
                result.contractors.push_back(std::move(v5c));
                ++id;
            }
        }
    }

    return result;
}

} // namespace xolver
