#include "theory/arith/icp/ContractorFactoryZ.h"
#include "theory/arith/icp/contractors/RelationContractorZ.h"
#include "theory/arith/icp/contractors/SquareContractorZ.h"

namespace nlcolver {

ContractorFactoryZ::BuildResult ContractorFactoryZ::build(
    const std::vector<IcpConstraint>& constraints,
    PolynomialKernel& kernel) {

    BuildResult result;
    size_t id = 0;

    for (const auto& c : constraints) {
        std::unique_ptr<ContractorZ> contractor;

        // 1. Try SquareContractorZ
        auto sq = std::make_unique<SquareContractorZ>(c, kernel);
        {
            int sign;
            mpz_class constant;
            // Use a temporary box to test pattern recognition
            ReasonedBoxZ tmpBox;
            tmpBox.set("_", ReasonedInterval{IntervalZ{0,0}, {}});
            // Actually, we need a way to test recognition without a box.
            // For now, just try it and if contract returns NoChange on first call, we keep it.
            // Better: add a static recognize method or check in factory.
            // Simplification: always create SquareContractorZ; it will NoChange if pattern doesn't match.
            contractor = std::move(sq);
        }

        // TODO: 2. Try SumSquaresContractorZ (V1 stub)

        // 3. Fallback: RelationContractorZ
        if (!contractor) {
            contractor = std::make_unique<RelationContractorZ>(c, kernel);
        }

        // Actually, let's just create both and let the engine try them.
        // But the plan says dispatch order: Square -> SumSquares -> Relation.
        // For V1, we can create a single contractor per constraint that tries patterns internally.
        // Simpler: create SquareContractorZ for all; it handles its own pattern check.
        // If it doesn't match, it returns NoChange quickly.
        // For constraints that are not squares, create RelationContractorZ as fallback.
        // But we need to know which one to create. Let's check if it's a square pattern.

        // Reset and do proper dispatch:
        contractor.reset();

        // Try SquareContractorZ
        auto sqTest = std::make_unique<SquareContractorZ>(c, kernel);
        // We need a way to check if the pattern matches without a box.
        // For now, we'll just create it. The contract() method will check the pattern.
        // To avoid creating useless contractors, we can check variables count.
        auto vars = kernel.variables(c.poly);
        if (vars.size() == 1) {
            auto degOpt = kernel.degree(c.poly, vars[0]);
            if (degOpt && *degOpt == 2) {
                auto coeffsOpt = kernel.getIntegerCoefficients(c.poly, vars[0]);
                if (coeffsOpt && coeffsOpt->size() == 3 && (*coeffsOpt)[1] == 0) {
                    // Could be x^2 - c pattern
                    contractor = std::make_unique<SquareContractorZ>(c, kernel);
                }
            }
        }

        if (!contractor) {
            contractor = std::make_unique<RelationContractorZ>(c, kernel);
        }

        auto watchedVars = contractor->vars();
        for (const auto& v : watchedVars) {
            result.watchers.addWatcher(v, id);
        }
        result.contractors.push_back(std::move(contractor));
        ++id;
    }

    return result;
}

} // namespace nlcolver
