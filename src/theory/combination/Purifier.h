#pragma once
#include "expr/ir.h"
#include "theory/combination/SharedTermRegistry.h"
#include <vector>
#include <string>
#include <unordered_set>

namespace nlcolver {

/**
 * Purifier for Nelson-Oppen theory combination.
 *
 * Decomposes mixed assertions into:
 *   - Pure theory atoms (one owner each)
 *   - Bridge definitions: fresh_var = alien_subterm
 *   - Shared equality atoms between shared constants
 *
 * Runs BEFORE atomization. Operates directly on CoreIr.
 */
class Purifier {
public:
    Purifier(CoreIr& ir, SharedTermRegistry& registry, SortId boolSort);

    void run();

    const std::vector<ExprId>& bridgeAssertions() const { return bridgeAssertions_; }

private:
    CoreIr& ir_;
    SharedTermRegistry& registry_;
    SortId boolSortId_;

    std::vector<ExprId> bridgeAssertions_;
    uint32_t freshCounter_ = 0;
    std::unordered_map<ExprId, ExprId> cache_;

    bool containsUfApply(ExprId eid) const;
    bool containsArithmetic(ExprId eid) const;

    ExprId makeFreshVar(SortId sort);
    ExprId makeEq(ExprId lhs, ExprId rhs);

    TheoryId theoryOf(ExprId eid) const;

    ExprId purifyRec(ExprId eid);
    void purifyAssertion(ExprId eid);
    void registerEufVars(ExprId eid);
};

} // namespace nlcolver
