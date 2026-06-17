#include "theory/combination/Purifier.h"
#include "util/EnvParam.h"
#include "theory/core/DebugTrace.h"
#include "expr/ir.h"
#include <unordered_set>
#include <functional>
#include <iostream>
#include <cstdlib>

namespace xolver {

// Phase 1 (XOLVER_COMB_UFARG_ARRANGE / XOLVER_COMB_SAT_FLOOR): whether to bridge
// a COMPOUND arith argument of a UF application into a fresh shared leaf. Gated
// so the default purified form is unchanged; active when either the certificate
// floor (needs the bridge var to SEE the obligation) or the arrangement (needs
// it to SPLIT and recover) is enabled.
static bool ufArgBridgeEnabled() {
    return xolver::env::diag("XOLVER_COMB_SAT_FLOOR") ||
           xolver::env::diag("XOLVER_COMB_UFARG_ARRANGE");
}

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

bool Purifier::isArrayOp(const CoreExpr& e) {
    return e.kind == Kind::Select || e.kind == Kind::Store ||
           e.kind == Kind::ConstArray;
}

bool Purifier::isCompoundArith(ExprId eid) const {
    const auto& e = ir_.get(eid);
    switch (e.kind) {
        case Kind::Add: case Kind::Sub: case Kind::Neg:
        case Kind::Mul: case Kind::Div: case Kind::Mod:
        case Kind::Abs: case Kind::Pow:
        case Kind::ToInt: case Kind::ToReal:
            return true;
        default:
            return false;
    }
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
    // iter-67: addShared so identical bridge equalities collapse.
    return ir_.addShared(e);
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
            // Skip array-sorted variables: they are EUF/array-internal, not
            // arith-shared. Registering them as shared terms would make a
            // plain array equality (= a b) look like a shared-equality atom
            // and steal it from the array reasoner's Extensionality path.
            if (ir_.arraySortParams(e.sort)) continue;
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

            // Array operator (select/store/const-array): the array argument
            // recurses normally (it stays in EUF), but every arith index /
            // element argument must become a shared leaf. Register all leaf
            // index/element vars+consts as shared terms (owned by EUF AND the
            // arith theory) here so bare-variable indices flow as interface
            // equalities; compound arith children are bridged on the second
            // visit below.
            if (isArrayOp(e)) {
                for (ExprId arg : e.children) {
                    registerEufVars(arg);
                }
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
            bool bridgeArgs = ufArgBridgeEnabled();
            for (ExprId arg : e.children) {
                ExprId p = done.at(arg);
                // Phase 1: a COMPOUND arith argument (e.g. f(i+1)) is bridged
                // into a fresh SHARED leaf — fresh = (i+1) routed to arith,
                // f(fresh) to EUF — mirroring the array-op path below. Without
                // this the arg stays an arith compound EUF cannot reason about,
                // so a congruence f(i+1) ≅ f(k) (k provably = i+1) stays
                // undischarged and the combination reports a false SAT. With the
                // bridge it becomes the same shape as f over two shared scalars,
                // which the certificate detector and arrangement handle.
                if (bridgeArgs && isCompoundArith(p)) {
                    auto cit = ufArgBridgeCache_.find(p);
                    if (cit != ufArgBridgeCache_.end()) {
                        p = cit->second;  // reuse the bridge var for an identical arg
                    } else {
                        ExprId fresh = makeFreshVar(ir_.get(p).sort);
                        bridgeAssertions_.push_back(makeEq(fresh, p));
                        ufArgBridgeCache_[p] = fresh;
                        p = fresh;
                    }
                }
                if (p != arg) changed = true;
                newArgs.push_back(p);
            }
            // Preserve the original UFApply payload (the function NAME). A
            // rebuilt apply with an empty payload gets a distinct EUF function
            // symbol, so congruence between e.g. f(bridge_0) and f(5) would
            // never fire — silently dropping the very equality combination
            // exists to exchange.
            ExprId purifiedApply = changed
                ? ir_.addShared(CoreExpr{Kind::UFApply, e.sort, SmallVector<ExprId, 4>(newArgs.begin(), newArgs.end()), e.payload})
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

        // Array operator: rebuild with purified children, and additionally
        // bridge any child that is a COMPOUND arith term (e.g. select(a,i+1))
        // so the index/element becomes a fresh shared leaf both EUF and the
        // arith theory observe. Bare variables / constants are left as-is —
        // they are already shared via registerEufVars. The array argument of a
        // store/select is never bridged (it is array-sorted, EUF-internal).
        if (isArrayOp(e)) {
            std::vector<ExprId> newChildren;
            newChildren.reserve(e.children.size());
            bool changed = false;
            for (size_t ci = 0; ci < e.children.size(); ++ci) {
                ExprId child = e.children[ci];
                ExprId p = done.at(child);   // purified subterm (alien UF lifted)
                // Index/element positions: child 0 of ConstArray is the value;
                // for select/store child 0 is the array (skip), the rest are
                // index/element (Int/Real-sorted).
                bool isArrayArg = (e.kind != Kind::ConstArray && ci == 0);
                if (!isArrayArg && isCompoundArith(p)) {
                    ExprId fresh = makeFreshVar(ir_.get(p).sort);
                    ExprId bridge = makeEq(fresh, p);
                    bridgeAssertions_.push_back(bridge);
                    p = fresh;
                }
                if (p != child) changed = true;
                newChildren.push_back(p);
            }
            ExprId rebuilt;
            if (!changed) {
                rebuilt = f.eid;
            } else {
                CoreExpr ne;
                ne.kind = e.kind;
                ne.sort = e.sort;
                ne.payload = e.payload;   // preserve payload (robustness; array ops
                                          // take their symbol from builtinName, but
                                          // keep it consistent with the other paths)
                for (ExprId c : newChildren) ne.children.push_back(c);
                rebuilt = ir_.addShared(ne);
            }

            // An array READ whose result is arithmetic (Int/Real) is, to the
            // arith theory, an alien term — bridge it into a fresh SHARED
            // variable exactly like a UFApply. `(> (select a i) 5)` thus
            // becomes `(> selbridge 5)` with the array-read equality
            // `(= selbridge (select a i))` routed to EUF. This couples the
            // read value to arithmetic soundly and is context-free (so it is
            // robust to a select appearing in both arith and non-arith
            // positions). Store/ConstArray results stay array-sorted and are
            // never bridged.
            if (e.kind == Kind::Select &&
                (e.sort == ir_.intSortId() || e.sort == ir_.realSortId())) {
                ExprId fresh = makeFreshVar(e.sort);
                ExprId bridge = makeEq(fresh, rebuilt);
                bridgeAssertions_.push_back(bridge);
                cache_[f.eid] = fresh;
                done[f.eid] = fresh;
            } else {
                done[f.eid] = rebuilt;
            }
            stack.pop_back();
            continue;
        }

        // A datatype SELECTOR whose result is arithmetic (Int/Real) is, to the
        // arith theory, an alien term — bridge it into a fresh SHARED variable
        // exactly like an array read. `(< (head x) 0)` becomes `(< selbridge 0)`
        // with the equality `(= selbridge (head x))` routed to EUF/DT (it
        // mentions a selector). The DtReasoner's projection lemma then
        // propagates head(x)=field into the shared var, coupling DT structure to
        // arithmetic. Bridged unconditionally when arith-sorted (context-free).
        if (e.kind == Kind::Selector &&
            (e.sort == ir_.intSortId() || e.sort == ir_.realSortId())) {
            std::vector<ExprId> selChildren;
            selChildren.reserve(e.children.size());
            bool selChanged = false;
            for (ExprId child : e.children) {
                ExprId p = done.at(child);
                if (p != child) selChanged = true;
                selChildren.push_back(p);
            }
            ExprId rebuilt;
            if (!selChanged) {
                rebuilt = f.eid;
            } else {
                CoreExpr ne;
                ne.kind = e.kind;
                ne.sort = e.sort;
                ne.payload = e.payload;   // preserve the selector name
                for (ExprId c : selChildren) ne.children.push_back(c);
                rebuilt = ir_.addShared(ne);
            }
            ExprId fresh = makeFreshVar(e.sort);
            ExprId bridge = makeEq(fresh, rebuilt);
            bridgeAssertions_.push_back(bridge);
            cache_[f.eid] = fresh;
            done[f.eid] = fresh;
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
            ne.payload = e.payload;   // #72 ROOT: preserve the node's payload — a
            // datatype Constructor/Tester (and any payload-bearing node) rebuilt
            // here with a purified COMPOUND child (e.g. mk(snd q, 0), is-mk(mk(...)))
            // otherwise loses its name and interns as a bare "#dt.ctor."/"#dt.is.",
            // breaking selector projection, the constructor-clash symbol compare,
            // and tester-consistency -> false sat AND false unsat (#70). The
            // Selector branch above already preserves it; this default branch did
            // not, so any compound-arg ctor/tester fell through and was stripped.
            for (ExprId c : newChildren) ne.children.push_back(c);
            done[f.eid] = ir_.addShared(ne);
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
    ufArgBridgeCache_.clear();
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

    if (xolver::env::diag("EUF_DIAG")) {
        std::function<std::string(ExprId)> nameOf = [&](ExprId e) -> std::string {
            const auto& ex = ir_.get(e);
            if (ex.kind == Kind::Variable) {
                if (auto* s = std::get_if<std::string>(&ex.payload.value)) return *s;
            }
            if (ex.isConst()) {
                if (auto* i = std::get_if<int64_t>(&ex.payload.value)) return std::to_string(*i);
                if (auto* s = std::get_if<std::string>(&ex.payload.value)) return *s;
            }
            if (ex.kind == Kind::UFApply) {
                std::string nm = std::get_if<std::string>(&ex.payload.value)
                                 ? std::get<std::string>(ex.payload.value) : "?fn";
                std::string r = nm + "(";
                for (size_t i = 0; i < ex.children.size(); ++i) {
                    if (i) r += ",";
                    r += nameOf(ex.children[i]);
                }
                return r + ")";
            }
            std::string r = "k" + std::to_string((int)ex.kind) + "[";
            for (size_t i = 0; i < ex.children.size(); ++i) {
                if (i) r += ",";
                r += nameOf(ex.children[i]);
            }
            return r + "]";
        };
        for (ExprId bridge : bridgeAssertions_) {
            const auto& b = ir_.get(bridge);
            if (b.children.size() == 2) {
                std::cerr << "[BRIDGE-DEF] " << nameOf(b.children[0]) << " := "
                          << nameOf(b.children[1]) << "\n";
            }
        }
        for (SharedTermId st : registry_.allSharedTerms()) {
            const auto* s = registry_.get(st);
            if (s) std::cerr << "[ST] st" << st << " = " << s->name
                             << " expr" << s->coreExpr << "\n";
        }
    }
}

} // namespace xolver
