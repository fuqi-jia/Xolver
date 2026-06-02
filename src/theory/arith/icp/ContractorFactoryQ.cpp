#include "theory/arith/icp/ContractorFactoryQ.h"
#include "theory/arith/icp/contractors/RelationContractorQ.h"
#include "theory/arith/icp/contractors/MonomialMultivariateContractorQ.h"

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
            // Multivariate: one V4 contractor per candidate live var. The
            // contractor itself rejects non-V4 shapes via isUsable() — we
            // drop those instead of registering them. A polynomial that
            // doesn't match V4 for ANY variable contributes zero contractors.
            for (const auto& liveVar : vars) {
                auto contractor = std::make_unique<MonomialMultivariateContractorQ>(
                    c, kernel, liveVar);
                if (!contractor->isUsable()) continue;
                for (const auto& w : contractor->vars()) {
                    result.watchers.addWatcher(w, id);
                }
                result.contractors.push_back(std::move(contractor));
                ++id;
            }
        }
    }

    return result;
}

} // namespace xolver
