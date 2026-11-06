#pragma once

#include "search/presolve/Presolve.h"
#include "base/WorkBudget.h"
#include <unordered_map>

namespace xolver {

using PolynomialDefinitions = std::map<VarId, RationalPolynomial>;

// Resolve an acyclic definition graph exactly. Missing dependencies, conflicting
// preassigned values and cycles leave the caller's assignment unchanged.
bool reconstructPolynomialDefinitions(const PolynomialDefinitions& definitions,
    std::unordered_map<VarId, mpq_class>& assignment, WorkBudget& work);

// Immutable hand-off from presolve to integer or real search. Reduced feasibility
// still needs reconstruction and validation against the original constraints.
class PresolveProjection {
public:
    struct Constraint {
        PolyId poly;
        Relation rel;
        std::vector<SatLit> premises;
    };

    static std::optional<PresolveProjection> build(const PresolveState& state,
                                                  WorkBudget& work);
    const std::vector<Constraint>& constraints() const { return constraints_; }
    const std::vector<SatLit>& premises() const { return premises_; }
    const std::set<VarId>& variables() const { return variables_; }
    size_t definitionCount() const { return definitions_.size(); }
    bool reconstruct(std::unordered_map<VarId, mpq_class>& assignment,
                     WorkBudget& work) const;

private:
    std::vector<Constraint> constraints_;
    std::vector<SatLit> premises_;
    std::set<VarId> variables_;
    std::set<VarId> freeVariables_;
    PolynomialDefinitions definitions_;
    bool integerDomain_ = false;
};

} // namespace xolver
