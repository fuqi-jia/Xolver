#include "theory/combination/Purifier.h"
#include "theory/core/DebugTrace.h"
#include "expr/ir.h"
#include <unordered_set>

namespace nlcolver {

Purifier::Purifier(CoreIr& ir, SharedTermRegistry& registry, SortId boolSort)
    : ir_(ir), registry_(registry), boolSortId_(boolSort) {}

bool Purifier::containsUfApply(ExprId eid) const {
    std::vector<ExprId> stack;
    stack.push_back(eid);
    std::unordered_set<ExprId> visited;
    while (!stack.empty()) {
        ExprId cur = stack.back();
        stack.pop_back();
        if (!visited.insert(cur).second) continue;
        const auto& e = ir_.get(cur);
        if (e.kind == Kind::UFApply) return true;
        for (ExprId child : e.children) {
            stack.push_back(child);
        }
    }
    return false;
}

bool Purifier::containsArithmetic(ExprId eid) const {
    std::vector<ExprId> stack;
    stack.push_back(eid);
    std::unordered_set<ExprId> visited;
    while (!stack.empty()) {
        ExprId cur = stack.back();
        stack.pop_back();
        if (!visited.insert(cur).second) continue;
        const auto& e = ir_.get(cur);
        if (e.kind == Kind::Add || e.kind == Kind::Sub || e.kind == Kind::Neg ||
            e.kind == Kind::Mul || e.kind == Kind::Div || e.kind == Kind::Mod ||
            e.kind == Kind::Abs || e.kind == Kind::Pow) {
            return true;
        }
        for (ExprId child : e.children) {
            stack.push_back(child);
        }
    }
    return false;
}

ExprId Purifier::makeFreshVar(SortId sort) {
    std::string name = "bridge_" + std::to_string(freshCounter_++);
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = sort;
    e.payload.value = name;
    ExprId id = ir_.add(e);
    // Register in SharedTermRegistry so it appears in allSharedTerms()
    SharedTermId stid = registry_.getOrCreate(id, sort, name, true);
    registry_.addOwner(stid, TheoryId::Combination);
    registry_.addOwner(stid, TheoryId::EUF);
    registry_.addOwner(stid, arithTheory_);
    NO_DBG << "[Purifier] makeFreshVar " << name << " stid=" << stid << "\n";
    return id;
}

ExprId Purifier::makeEq(ExprId lhs, ExprId rhs) {
    CoreExpr e;
    e.kind = Kind::Eq;
    e.sort = boolSortId_;
    e.children.push_back(lhs);
    e.children.push_back(rhs);
    return ir_.add(e);
}

TheoryId Purifier::theoryOf(ExprId eid) const {
    if (containsUfApply(eid)) return TheoryId::EUF;
    if (containsArithmetic(eid)) return arithTheory_;
    return TheoryId::EUF;
}

void Purifier::registerEufVars(ExprId eid) {
    std::vector<ExprId> stack;
    stack.push_back(eid);
    std::unordered_set<ExprId> visited;
    while (!stack.empty()) {
        ExprId cur = stack.back();
        stack.pop_back();
        if (!visited.insert(cur).second) continue;
        const auto& e = ir_.get(cur);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                SharedTermId id = registry_.getOrCreate(cur, e.sort, *s, false);
                registry_.addOwner(id, TheoryId::EUF);
                registry_.addOwner(id, arithTheory_);
            }
            continue;
        }
        if (e.isConst()) {
            std::string name;
            if (auto* b = std::get_if<bool>(&e.payload.value)) {
                name = *b ? "true" : "false";
            } else if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
                name = std::to_string(*i);
            } else if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                name = *s;
            } else if (auto* bv = std::get_if<uint64_t>(&e.payload.value)) {
                name = "bv" + std::to_string(*bv);
            }
            if (!name.empty()) {
                SharedTermId id = registry_.getOrCreate(cur, e.sort, name, false);
                registry_.addOwner(id, TheoryId::EUF);
                registry_.addOwner(id, arithTheory_);
            }
            continue;
        }
        for (ExprId child : e.children) {
            stack.push_back(child);
        }
    }
}

ExprId Purifier::purifyRec(ExprId root) {
    // Fast path: already in global cache
    auto it = cache_.find(root);
    if (it != cache_.end()) return it->second;

    struct Frame {
        ExprId eid;
        bool childrenDone;  // false = first visit, true = children processed
    };

    std::vector<Frame> stack;
    std::unordered_map<ExprId, ExprId> done;  // local results for this invocation

    auto tryResolve = [&](ExprId eid) -> bool {
        const auto& e = ir_.get(eid);
        // Leaf
        if (e.kind == Kind::Variable || e.kind == Kind::ConstBool ||
            e.kind == Kind::ConstInt || e.kind == Kind::ConstReal ||
            e.kind == Kind::ConstBV || e.kind == Kind::ConstFP) {
            done[eid] = eid;
            return true;
        }
        // Already in global cache
        auto git = cache_.find(eid);
        if (git != cache_.end()) {
            done[eid] = git->second;
            return true;
        }
        // Already computed in this invocation
        if (done.count(eid)) return true;
        return false;
    };

    if (!tryResolve(root)) {
        stack.push_back(Frame{root, false});
    }

    while (!stack.empty()) {
        Frame& f = stack.back();
        if (f.eid >= ir_.size()) {
            done[f.eid] = f.eid;
            stack.pop_back();
            continue;
        }
        // Use value copy because ir_.add() below may reallocate exprs_ vector,
        // invalidating any prior reference.
        const CoreExpr e = ir_.get(f.eid);

        if (!f.childrenDone) {
            // First visit
            f.childrenDone = true;

            // UFApply -> bridge variable
            if (e.kind == Kind::UFApply) {
                for (ExprId arg : e.children) {
                    registerEufVars(arg);
                }
                // Push args in reverse so they are processed left-to-right
                for (size_t i = e.children.size(); i-- > 0; ) {
                    if (!tryResolve(e.children[i])) {
                        stack.push_back(Frame{e.children[i], false});
                    }
                }
                continue;
            }

            // Default: recurse into children
            for (size_t i = e.children.size(); i-- > 0; ) {
                if (!tryResolve(e.children[i])) {
                    stack.push_back(Frame{e.children[i], false});
                }
            }
            continue;
        }

        // Second visit: children are resolved in `done`
        // UFApply -> bridge variable
        if (e.kind == Kind::UFApply) {
            std::vector<ExprId> newArgs;
            newArgs.reserve(e.children.size());
            bool changed = false;
            for (ExprId arg : e.children) {
                ExprId p = done.at(arg);
                if (p != arg) changed = true;
                newArgs.push_back(p);
            }
            ExprId purifiedApply = changed
                ? ir_.add(CoreExpr{Kind::UFApply, e.sort, SmallVector<ExprId, 4>(newArgs.begin(), newArgs.end()), Payload{}})
                : f.eid;
            ExprId fresh = makeFreshVar(e.sort);
            ExprId bridge = makeEq(fresh, purifiedApply);
            bridgeAssertions_.push_back(bridge);
            cache_[f.eid] = fresh;
            done[f.eid] = fresh;
            NO_DBG << "[Purifier] bridge eid=" << f.eid << " -> eid=" << fresh
                   << " bridge=" << bridge << "\n";
            stack.pop_back();
            continue;
        }

        // Default branch
        std::vector<ExprId> newChildren;
        newChildren.reserve(e.children.size());
        bool changed = false;
        for (ExprId child : e.children) {
            ExprId p = done.at(child);
            if (p != child) changed = true;
            newChildren.push_back(p);
        }
        if (!changed) {
            done[f.eid] = f.eid;
        } else {
            CoreExpr ne;
            ne.kind = e.kind;
            ne.sort = e.sort;
            for (ExprId c : newChildren) ne.children.push_back(c);
            done[f.eid] = ir_.add(ne);
        }
        stack.pop_back();
    }

    return done.at(root);
}

void Purifier::purifyAssertion(ExprId eid) {
    (void)eid;
}

void Purifier::run() {
    std::vector<ExprId> original = ir_.assertions();
    std::vector<ExprId> purified;
    bridgeAssertions_.clear();
    cache_.clear();
    freshCounter_ = 0;

    for (ExprId eid : original) {
        registerEufVars(eid);
    }

    for (ExprId eid : original) {
        ExprId p = purifyRec(eid);
        purified.push_back(p);
    }

    // Debug removed

    ir_.replaceAssertions(purified);

    for (ExprId bridge : bridgeAssertions_) {
        ir_.addAssertion(bridge);
    }
}

} // namespace nlcolver
