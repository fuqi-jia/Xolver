#include "search/boolean/TheoryRefutation.h"
#include <algorithm>
#include "base/WorkBudget.h"

namespace xolver {
BooleanRefutationResult refuteBooleanTheory(
    SatSolver& sat, const RefutationAssignment& select,
    const TheoryRefutationOracle& oracle, const BooleanRefutationLimits& limits) {
    BooleanRefutationResult result;
    if (!select || !oracle) return result;
    sat.setDeadline(limits.deadline);
    try {
        for (size_t trial = 0; trial < limits.assignments; ++trial) {
            if (std::chrono::steady_clock::now() >= limits.deadline) {
                result.exhausted = true;
                return result;
            }
            sat.limit("conflicts", limits.satConflicts);
            const auto answer = sat.solve();
            if (answer == SatSolver::SolveResult::Unsat) {
                result.refuted = true;
                return result;
            }
            if (answer != SatSolver::SolveResult::Sat) { result.exhausted = true; return result; }
            auto assignment = select(sat);
            ++result.assignments;
            for (auto literal : assignment)
                if (!literal.var || sat.value(literal.var) != literal.sign) return result;
            auto conflict = oracle(assignment);
            if (!conflict || conflict->empty()) return result;
            std::vector<SatLit> clause;
            for (auto premise : *conflict) {
                if (std::find(assignment.begin(), assignment.end(), premise) == assignment.end())
                    return result;
                const auto negated = premise.negated();
                if (std::find(clause.begin(), clause.end(), negated) == clause.end())
                    clause.push_back(negated);
            }
            // The learned clause is a theory tautology, never original Boolean input.
            sat.addTheoryClause(clause);
            ++result.conflicts;
            if (sat.inconsistent()) {
                result.refuted = true;
                return result;
            }
        }
        result.exhausted = true;
    } catch (const ResourceExhausted&) {
        result.exhausted = true;
    }
    return result;
}
} // namespace xolver
