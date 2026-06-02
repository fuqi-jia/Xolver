#include "theory/arith/icp/ContractorFactoryQ.h"
#include "theory/arith/icp/contractors/RelationContractorQ.h"

namespace xolver {

ContractorFactoryQ::BuildResult ContractorFactoryQ::build(
    const std::vector<IcpConstraint>& constraints,
    PolynomialKernel& kernel) {

    BuildResult result;
    size_t id = 0;

    for (const auto& c : constraints) {
        // V1: only univariate atoms are useful — RelationContractorQ checks
        // arity itself, but skipping zero/multi-var here saves a factory entry.
        if (c.poly == NullPoly) continue;
        auto vars = kernel.variables(c.poly);
        if (vars.size() != 1) continue;

        auto contractor = std::make_unique<RelationContractorQ>(c, kernel);
        for (const auto& v : contractor->vars()) {
            result.watchers.addWatcher(v, id);
        }
        result.contractors.push_back(std::move(contractor));
        ++id;
    }

    return result;
}

} // namespace xolver
