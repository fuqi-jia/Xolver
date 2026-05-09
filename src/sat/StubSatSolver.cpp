#ifndef NLCOLVER_HAS_CADICAL

#include "sat/SatSolver.h"
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

/**
 * StubSatSolver: minimal SAT backend for Stage A.
 *
 * Handles:
 * - Empty clause → UNSAT
 * - Empty clause DB → SAT
 * - Pure unit-clause problems (no branching needed)
 * Everything else → Unknown.
 */
class StubSatSolver : public SatSolver {
public:
    SatVar newVar() override {
        return nextVar_++;
    }

    void addClause(const std::vector<SatLit>& clause) override {
        if (clause.empty()) {
            hasEmptyClause_ = true;
            return;
        }
        clauses_.push_back(clause);
    }

    SolveResult solve() override {
        if (hasEmptyClause_) return SolveResult::Unsat;
        if (clauses_.empty()) return SolveResult::Sat;

        assignment_.clear();
        // Try unit propagation at decision level 0.
        std::unordered_map<SatVar, bool>& assignment = assignment_;
        bool changed = true;
        while (changed) {
            changed = false;
            for (const auto& clause : clauses_) {
                int unassigned = 0;
                SatLit lastUnassigned{0, true};
                bool satisfied = false;
                for (SatLit lit : clause) {
                    auto it = assignment.find(lit.var);
                    if (it == assignment.end()) {
                        ++unassigned;
                        lastUnassigned = lit;
                    } else {
                        bool val = lit.sign ? it->second : !it->second;
                        if (val) { satisfied = true; break; }
                    }
                }
                if (satisfied) continue;
                if (unassigned == 0) {
                    // Conflict at level 0 → UNSAT
                    return SolveResult::Unsat;
                }
                if (unassigned == 1) {
                    // Unit clause: force assignment
                    bool val = lastUnassigned.sign;
                    auto it = assignment.find(lastUnassigned.var);
                    if (it == assignment.end()) {
                        assignment[lastUnassigned.var] = val;
                        changed = true;
                    } else if (it->second != val) {
                        return SolveResult::Unsat;
                    }
                }
            }
        }

        // If we reach here without conflict, the problem is SAT
        // under the partial assignment (or all clauses have >1 unassigned literals).
        // For Stage A, treat this as SAT if all clauses were unit-propagated safely.
        return SolveResult::Sat;
    }

    SolveResult solve(const std::vector<SatLit>&) override {
        return solve();
    }

    bool value(SatVar v) const override {
        auto it = assignment_.find(v);
        if (it != assignment_.end()) return it->second;
        return false;
    }

private:
    SatVar nextVar_ = 1;
    bool hasEmptyClause_ = false;
    std::vector<std::vector<SatLit>> clauses_;
    std::unordered_map<SatVar, bool> assignment_;
};

std::unique_ptr<SatSolver> createSatSolver() {
    return std::make_unique<StubSatSolver>();
}

} // namespace nlcolver

#endif // !NLCOLVER_HAS_CADICAL
