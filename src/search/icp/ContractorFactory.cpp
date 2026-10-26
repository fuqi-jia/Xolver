#include "search/icp/ContractorFactory.h"
#include "search/icp/contractors/RelationContractor.h"
#include "search/icp/contractors/SquareContractor.h"

namespace xolver {

ContractorFactory::BuildResult ContractorFactory::build(
    const std::vector<IcpConstraint>& constraints,
    PolynomialKernel& kernel) {
    BuildResult result;
    auto add = [&](std::unique_ptr<Contractor> contractor) {
        const auto id = result.contractors.size();
        for (const auto& var : contractor->vars()) result.watchers.addWatcher(var, id);
        result.contractors.push_back(std::move(contractor));
    };

    for (const auto& constraint : constraints) {
        const auto vars = kernel.variables(constraint.poly);
        const auto degree = vars.size() == 1 ? kernel.degree(constraint.poly, vars.front()) : std::nullopt;
        if (degree && *degree == 2) {
            const auto coefficients = kernel.getIntegerCoefficients(constraint.poly, vars.front());
            if (coefficients && coefficients->size() == 3 && (*coefficients)[1] == 0 &&
                ((*coefficients)[0] == 1 || (*coefficients)[0] == -1)) {
                add(std::make_unique<SquareContractor>(constraint, kernel));
            }
        }
        // Square contraction is complementary to interval evaluation. It may
        // decline a relation (e.g. disequality) or leave an interval that the
        // original relation can refute; retain that check for every polynomial.
        add(std::make_unique<RelationContractor>(constraint, kernel));
    }
    return result;
}

} // namespace xolver
