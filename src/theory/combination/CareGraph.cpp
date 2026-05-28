#include "theory/combination/CareGraph.h"
#include "theory/combination/SharedTermRegistry.h"
#include "expr/ir.h"
#include <vector>

namespace xolver {

void CareGraph::build(const CoreIr& ir, const SharedTermRegistry& reg) {
    care_.clear();

    auto markIfShared = [&](ExprId e) {
        if (auto st = reg.findByExprId(e)) care_.insert(*st);
    };

    // Internal bridge variables (Purifier output) are always care-relevant:
    // each is defined equal to a UFApply / array read and stands in for an
    // alien term, so its interface (dis)equalities can fire EUF inferences.
    for (SharedTermId st : reg.allSharedTerms()) {
        if (const auto* s = reg.get(st)) {
            if (s->isInternal) care_.insert(st);
        }
    }

    // Single DAG walk over all (purified) assertions. Mark the shared operands
    // of the inference-bearing node kinds.
    std::vector<ExprId> stack = ir.assertions();
    std::unordered_set<ExprId> visited;
    while (!stack.empty()) {
        ExprId cur = stack.back();
        stack.pop_back();
        if (!visited.insert(cur).second) continue;
        const auto& e = ir.get(cur);
        switch (e.kind) {
            case Kind::UFApply:
            case Kind::Select:
            case Kind::Store:
            case Kind::ConstArray:
            case Kind::Eq:
            case Kind::Distinct:
                for (ExprId c : e.children) markIfShared(c);
                break;
            default:
                break;
        }
        for (ExprId c : e.children) stack.push_back(c);
    }

    built_ = true;
}

} // namespace xolver
