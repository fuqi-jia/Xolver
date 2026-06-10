#include "theory/arith/icp/ContractorFactory.h"
#include "theory/arith/icp/contractors/RelationContractor.h"
#include "theory/arith/icp/contractors/SquareContractor.h"

namespace xolver {

ContractorFactory::BuildResult ContractorFactory::build(
    const std::vector<IcpConstraint>& constraints,
    PolynomialKernel& kernel) {

    BuildResult result;
    size_t id = 0;

    for (const auto& c : constraints) {
        std::unique_ptr<Contractor> contractor;

        // 1. Try SquareContractor
        auto sq = std::make_unique<SquareContractor>(c, kernel);
        {
            // int sign;   // unused
            // mpz_class constant;  // unused
            // Use a temporary box to test pattern recognition
            ReasonedBox tmpBox;
            tmpBox.set("_", ReasonedInterval{IntervalZ{0,0}, {}});
            // Actually, we need a way to test recognition without a box.
            // For now, just try it and if contract returns NoChange on first call, we keep it.
            // Better: add a static recognize method or check in factory.
            // Simplification: always create SquareContractor; it will NoChange if pattern doesn't match.
            contractor = std::move(sq);
        }

        // TODO: 2. Try SumSquaresContractor (V1 stub)

        // 3. Fallback: RelationContractor
        if (!contractor) {
            contractor = std::make_unique<RelationContractor>(c, kernel);
        }

        // Actually, let's just create both and let the engine try them.
        // But the plan says dispatch order: Square -> SumSquares -> Relation.
        // For V1, we can create a single contractor per constraint that tries patterns internally.
        // Simpler: create SquareContractor for all; it handles its own pattern check.
        // If it doesn't match, it returns NoChange quickly.
        // For constraints that are not squares, create RelationContractor as fallback.
        // But we need to know which one to create. Let's check if it's a square pattern.

        // Reset and do proper dispatch:
        contractor.reset();

        // Try SquareContractor
        auto sqTest = std::make_unique<SquareContractor>(c, kernel);
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
                    contractor = std::make_unique<SquareContractor>(c, kernel);
                }
            }
        }

        if (!contractor) {
            contractor = std::make_unique<RelationContractor>(c, kernel);
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

} // namespace xolver
