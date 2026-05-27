#include "frontend/preprocess/UnconditionalConstantPropagation.h"
#include <stdexcept>

namespace zolver {

UnconditionalConstantPropagation::UnconditionalConstantPropagation(CoreIr& ir)
    : ir_(ir),
      boolSortId_(ir.boolSortId()),
      intSortId_(ir.intSortId()),
      realSortId_(ir.realSortId()) {}

bool UnconditionalConstantPropagation::run() {
    fixedConstMap_.clear();
    substMemo_.clear();
    foldMemo_.clear();
    constCache_.clear();
    boolConstCache_.clear();
    rewrittenAssertions_.clear();
    contradiction_ = false;

    // Pre-populate the constant cache by scanning every existing
    // numeric and boolean constant in the IR. Once an ExprId for the
    // value-and-sort combination is known, materializeConstant /
    // mkBool reuse it; otherwise newly-folded constants would acquire
    // fresh ExprIds and break the relation-identity fold's
    // ExprId-equality assumption.
    for (size_t i = 0; i < ir_.size(); ++i) {
        ExprId id = static_cast<ExprId>(i);
        const auto& n = ir_.get(id);
        if (n.kind == Kind::ConstInt) {
            if (auto* v = std::get_if<int64_t>(&n.payload.value)) {
                std::string key = std::to_string(n.sort) + "#I:" + std::to_string(*v);
                constCache_.emplace(std::move(key), id);
            }
        } else if (n.kind == Kind::ConstReal) {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                std::string key = std::to_string(n.sort) + "#R:" + *s;
                constCache_.emplace(std::move(key), id);
            }
        } else if (n.kind == Kind::ConstBool) {
            if (auto* v = std::get_if<bool>(&n.payload.value)) {
                std::string key = std::to_string(n.sort) + "#B:" + (*v ? "1" : "0");
                boolConstCache_.emplace(std::move(key), id);
            }
        }
    }

    // Phase 1 — collection from unconditional conjuncts only.
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        (void)level;
        collectFromAssertion(eid);
        if (contradiction_) break;
    }
    if (contradiction_) {
        // The caller will short-circuit; we still copy the original
        // assertions so the IR is left in a consistent state if commit()
        // is called.
        for (const auto& [level, eid] : ir_.getScopedAssertions()) {
            rewrittenAssertions_.emplace_back(level, eid);
        }
        return true;
    }
    if (fixedConstMap_.empty()) {
        // Nothing to substitute; copy assertions verbatim.
        for (const auto& [level, eid] : ir_.getScopedAssertions()) {
            rewrittenAssertions_.emplace_back(level, eid);
        }
        return true;
    }

    // Phase 2 — global substitution into every assertion EXCEPT the
    // source-of-binding conjuncts themselves. Rewriting `(= x 1)` into
    // `(= 1 1)` would erase the structural information that the EUF /
    // arithmetic theory engines rely on for congruence and propagation
    // (we observed an unsoundness on `uflia_017` precisely because the
    // theory could no longer recover `x = 1` from the trivial residual
    // `1 = 1` and therefore failed to derive the congruence
    // `f(x+1) = f(2)`). Keeping the original equality literal preserves
    // the binding for downstream theories while propagating the
    // constant everywhere else.
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        rewrittenAssertions_.emplace_back(level, substituteAssertion(eid));
    }
    return true;
}

ExprId UnconditionalConstantPropagation::substituteAssertion(ExprId assertion) {
    // Value copy, not a reference: substituteRec(child) below calls ir_.add()
    // (and materializeConstant), which reallocates exprs_ and would dangle a
    // `const CoreExpr&` and its children iterators mid-loop (use-after-free).
    const auto node = ir_.get(assertion);
    if (node.kind == Kind::And) {
        // Per-conjunct: source-of-binding conjuncts are kept verbatim;
        // all other conjuncts are globally rewritten.
        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool changed = false;
        for (ExprId child : node.children) {
            ExprId rewritten = isSourceOfBinding(child)
                ? child
                : substituteRec(child);
            if (rewritten != child) changed = true;
            newChildren.push_back(rewritten);
        }
        if (!changed) return assertion;
        CoreExpr fresh;
        fresh.kind = node.kind;
        fresh.sort = node.sort;
        for (ExprId c : newChildren) fresh.children.push_back(c);
        fresh.payload = node.payload;
        return ir_.add(std::move(fresh));
    }
    if (isSourceOfBinding(assertion)) return assertion;
    ExprId substituted = substituteRec(assertion);
    foldMemo_.clear();
    return constantFoldRec(substituted);
}

ExprId UnconditionalConstantPropagation::constantFoldRec(ExprId root) {
    if (auto it = foldMemo_.find(root); it != foldMemo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack); avoids stack overflow on deep
    // terms. Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (foldMemo_.find(e) != foldMemo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: tryFold*/ir_.add relocate

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { foldMemo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (c != NullExpr && foldMemo_.find(c) == foldMemo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = (c == NullExpr) ? NullExpr : foldMemo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        ExprId rebuilt = e;
        if (changed) {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            for (ExprId c : newChildren) fresh.children.push_back(c);
            fresh.payload = node.payload;
            rebuilt = ir_.add(std::move(fresh));
        }
        // Try arithmetic, relation, and boolean folds at this node.
        ExprId folded = tryFoldArithmetic(rebuilt);
        if (folded == rebuilt) folded = tryFoldRelation(rebuilt);
        if (folded == rebuilt) folded = tryFoldBoolean(rebuilt);
        foldMemo_[e] = folded;
    }
    return foldMemo_.at(root);
}

ExprId UnconditionalConstantPropagation::tryFoldArithmetic(ExprId e) {
    const auto& node = ir_.get(e);
    auto isNumKind = [](Kind k) {
        return k == Kind::Add || k == Kind::Sub || k == Kind::Neg
            || k == Kind::Mul;
    };
    if (!isNumKind(node.kind)) return e;

    // Absorption / identity rules — applicable even when not every
    // child is a constant. Required because the downstream Atomizer
    // refuses to register atoms whose PolynomialConverter returns
    // Tautology/Conflict, leaving the SAT variable free and producing
    // unsoundness (cf. nra_012: after substituting `x → 0`, the
    // residual `(> (* 0 y) 0)` collapses to `(> 0 0)` ⇒ `false`, but
    // the Atomizer drops the atom and SAT picks it true).
    //
    // Multiplication: zero-absorption + one-identity, term-by-term.
    if (node.kind == Kind::Mul) {
        std::vector<ExprId> kept;
        kept.reserve(node.children.size());
        for (ExprId c : node.children) {
            auto v = tryAsConstNumeric(c);
            if (v && *v == 0) {
                // 0 * anything = 0  (sound: 0 absorbs).
                return materializeConstant(mpq_class(0), node.sort);
            }
            if (v && *v == 1) {
                // 1 * anything : drop the 1; keep the other factors.
                continue;
            }
            kept.push_back(c);
        }
        if (kept.empty()) {
            // All factors were 1 — product is 1.
            return materializeConstant(mpq_class(1), node.sort);
        }
        // If every kept child is a constant, fold the product.
        bool allConst = true;
        mpq_class product = 1;
        for (ExprId c : kept) {
            auto v = tryAsConstNumeric(c);
            if (!v) { allConst = false; break; }
            product *= *v;
        }
        if (allConst) return materializeConstant(product, node.sort);
        if (kept.size() == 1) return kept[0];
        if (kept.size() == node.children.size()) return e;
        // Otherwise rebuild a smaller Mul with the kept children.
        CoreExpr fresh;
        fresh.kind = Kind::Mul;
        fresh.sort = node.sort;
        for (ExprId c : kept) fresh.children.push_back(c);
        return ir_.add(std::move(fresh));
    }

    // Addition: zero-identity, term-by-term.
    if (node.kind == Kind::Add) {
        std::vector<ExprId> kept;
        kept.reserve(node.children.size());
        for (ExprId c : node.children) {
            auto v = tryAsConstNumeric(c);
            if (v && *v == 0) continue;     // 0 + x = x
            kept.push_back(c);
        }
        if (kept.empty()) {
            return materializeConstant(mpq_class(0), node.sort);
        }
        bool allConst = true;
        mpq_class sum = 0;
        for (ExprId c : kept) {
            auto v = tryAsConstNumeric(c);
            if (!v) { allConst = false; break; }
            sum += *v;
        }
        if (allConst) return materializeConstant(sum, node.sort);
        if (kept.size() == 1) return kept[0];
        if (kept.size() == node.children.size()) return e;
        CoreExpr fresh;
        fresh.kind = Kind::Add;
        fresh.sort = node.sort;
        for (ExprId c : kept) fresh.children.push_back(c);
        return ir_.add(std::move(fresh));
    }

    // Sub / Neg: require every operand to be a constant (no useful
    // identity rules because `a - 0` is fine but `0 - a` flips sign).
    std::vector<mpq_class> vals;
    vals.reserve(node.children.size());
    for (ExprId c : node.children) {
        auto v = tryAsConstNumeric(c);
        if (!v) return e;
        vals.push_back(*v);
    }
    mpq_class result;
    switch (node.kind) {
        case Kind::Sub:
            if (vals.empty()) return e;
            result = vals[0];
            for (size_t i = 1; i < vals.size(); ++i) result -= vals[i];
            break;
        case Kind::Neg:
            if (vals.size() != 1) return e;
            result = -vals[0];
            break;
        default: return e;
    }
    return materializeConstant(result, node.sort);
}

ExprId UnconditionalConstantPropagation::tryFoldRelation(ExprId e) {
    const auto& node = ir_.get(e);
    auto isRelKind = [](Kind k) {
        return k == Kind::Eq || k == Kind::Lt || k == Kind::Leq
            || k == Kind::Gt || k == Kind::Geq || k == Kind::Distinct;
    };
    if (!isRelKind(node.kind)) return e;
    if (node.children.size() < 2) return e;

    // Identity folds first: same-ExprId operands collapse the relation
    // regardless of value (CoreIr DAG-dedups identical sub-expressions,
    // so `(= (f 2) (f 2))` and `(distinct (f 2) (f 2))` arise from
    // substitution + arithmetic constant-fold under UF arguments).
    bool allChildrenEqual = node.children.size() >= 2;
    for (size_t i = 1; i < node.children.size() && allChildrenEqual; ++i) {
        if (node.children[i] != node.children[0]) allChildrenEqual = false;
    }
    if (allChildrenEqual) {
        switch (node.kind) {
            case Kind::Eq:       return mkBool(true);   // (= a a)
            case Kind::Leq:
            case Kind::Geq:      return mkBool(true);   // (≤ a a), (≥ a a)
            case Kind::Distinct: return mkBool(false);  // (distinct a a ...)
            case Kind::Lt:
            case Kind::Gt:       return mkBool(false);  // (< a a), (> a a)
            default: break;
        }
    }

    std::vector<mpq_class> vals;
    vals.reserve(node.children.size());
    for (ExprId c : node.children) {
        auto v = tryAsConstNumeric(c);
        if (!v) return e;
        vals.push_back(*v);
    }
    bool result;
    switch (node.kind) {
        case Kind::Eq:
            result = true;
            for (size_t i = 1; i < vals.size(); ++i)
                if (vals[i] != vals[0]) { result = false; break; }
            break;
        case Kind::Distinct: {
            result = true;
            for (size_t i = 0; i < vals.size() && result; ++i)
                for (size_t j = i + 1; j < vals.size() && result; ++j)
                    if (vals[i] == vals[j]) result = false;
            break;
        }
        case Kind::Lt:
            result = vals.size() == 2 && vals[0] <  vals[1]; break;
        case Kind::Leq:
            result = vals.size() == 2 && vals[0] <= vals[1]; break;
        case Kind::Gt:
            result = vals.size() == 2 && vals[0] >  vals[1]; break;
        case Kind::Geq:
            result = vals.size() == 2 && vals[0] >= vals[1]; break;
        default: return e;
    }
    return mkBool(result);
}

ExprId UnconditionalConstantPropagation::tryFoldBoolean(ExprId e) {
    const auto& node = ir_.get(e);
    if (node.kind == Kind::Not && node.children.size() == 1) {
        auto v = tryAsConstBool(node.children[0]);
        if (v) return mkBool(!*v);
        return e;
    }
    if (node.kind == Kind::And) {
        bool sawFalse = false;
        std::vector<ExprId> kept;
        kept.reserve(node.children.size());
        for (ExprId c : node.children) {
            auto v = tryAsConstBool(c);
            if (v) {
                if (*v) continue;       // true children drop
                sawFalse = true; break;
            }
            kept.push_back(c);
        }
        if (sawFalse) return mkBool(false);
        if (kept.empty()) return mkBool(true);
        if (kept.size() == 1) return kept[0];
        if (kept.size() == node.children.size()) return e;
        CoreExpr fresh;
        fresh.kind = Kind::And;
        fresh.sort = boolSortId_;
        for (ExprId c : kept) fresh.children.push_back(c);
        return ir_.add(std::move(fresh));
    }
    if (node.kind == Kind::Or) {
        bool sawTrue = false;
        std::vector<ExprId> kept;
        kept.reserve(node.children.size());
        for (ExprId c : node.children) {
            auto v = tryAsConstBool(c);
            if (v) {
                if (!*v) continue;      // false children drop
                sawTrue = true; break;
            }
            kept.push_back(c);
        }
        if (sawTrue) return mkBool(true);
        if (kept.empty()) return mkBool(false);
        if (kept.size() == 1) return kept[0];
        if (kept.size() == node.children.size()) return e;
        CoreExpr fresh;
        fresh.kind = Kind::Or;
        fresh.sort = boolSortId_;
        for (ExprId c : kept) fresh.children.push_back(c);
        return ir_.add(std::move(fresh));
    }
    return e;
}

std::optional<bool> UnconditionalConstantPropagation::tryAsConstBool(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind != Kind::ConstBool) return std::nullopt;
    if (auto* v = std::get_if<bool>(&node.payload.value)) return *v;
    return std::nullopt;
}

ExprId UnconditionalConstantPropagation::mkBool(bool value) {
    std::string key = std::to_string(boolSortId_) + "#B:" + (value ? "1" : "0");
    auto it = boolConstCache_.find(key);
    if (it != boolConstCache_.end()) return it->second;
    CoreExpr fresh;
    fresh.kind = Kind::ConstBool;
    fresh.sort = boolSortId_;
    fresh.payload = Payload(value);
    ExprId id = ir_.add(std::move(fresh));
    boolConstCache_[key] = id;
    return id;
}

bool UnconditionalConstantPropagation::isSourceOfBinding(ExprId conjunct) const {
    const auto& node = ir_.get(conjunct);
    if (node.kind != Kind::Eq || node.children.size() != 2) return false;
    auto tryRecord = [&](ExprId varSide, ExprId constSide) -> bool {
        const auto& vn = ir_.get(varSide);
        if (vn.kind != Kind::Variable) return false;
        auto* name = std::get_if<std::string>(&vn.payload.value);
        if (!name) return false;
        auto valueOpt = tryAsConstNumeric(constSide);
        if (!valueOpt) return false;
        auto it = fixedConstMap_.find(*name);
        return it != fixedConstMap_.end() && it->second == *valueOpt;
    };
    if (tryRecord(node.children[0], node.children[1])) return true;
    if (tryRecord(node.children[1], node.children[0])) return true;
    return false;
}

void UnconditionalConstantPropagation::collectFromAssertion(ExprId assertion) {
    const auto& node = ir_.get(assertion);
    if (node.kind == Kind::And) {
        // Flatten — every direct child is also unconditional.
        for (ExprId child : node.children) {
            collectFromConjunct(child);
            if (contradiction_) return;
        }
    } else {
        collectFromConjunct(assertion);
    }
}

void UnconditionalConstantPropagation::collectFromConjunct(ExprId conjunct) {
    auto tryRecord = [&](ExprId varSide, ExprId constSide) -> bool {
        const auto& vn = ir_.get(varSide);
        if (vn.kind != Kind::Variable) return false;
        auto* name = std::get_if<std::string>(&vn.payload.value);
        if (!name) return false;
        auto valueOpt = tryAsConstNumeric(constSide);
        if (!valueOpt) return false;
        return tryRecordBinding(*name, *valueOpt);
    };

    // Iteratively flatten nested unconditional Ands (avoids deep recursion on
    // redundantly-wrapped conjunctions). Reverse-push so children pop in source
    // order, matching the former recursion.
    std::vector<ExprId> work;
    work.push_back(conjunct);
    while (!work.empty()) {
        if (contradiction_) return;
        ExprId e = work.back();
        work.pop_back();
        const auto& node = ir_.get(e);
        if (node.kind == Kind::And) {
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i)
                work.push_back(node.children[i]);
            continue;
        }
        if (node.kind != Kind::Eq || node.children.size() != 2) continue;
        if (tryRecord(node.children[0], node.children[1])) continue;
        tryRecord(node.children[1], node.children[0]);
    }
}

bool UnconditionalConstantPropagation::tryRecordBinding(
    const std::string& varName, const mpq_class& value) {
    auto it = fixedConstMap_.find(varName);
    if (it == fixedConstMap_.end()) {
        fixedConstMap_[varName] = value;
        return true;
    }
    if (it->second != value) {
        contradiction_ = true;
        return false;
    }
    return true;
}

std::optional<mpq_class>
UnconditionalConstantPropagation::tryAsConstNumeric(ExprId e) const {
    const auto& node = ir_.get(e);
    if (node.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&node.payload.value)) {
            return mpq_class(*v);
        }
        return std::nullopt;
    }
    if (node.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&node.payload.value)) {
            try {
                return mpq_class(*s);
            } catch (...) {
                return std::nullopt;
            }
        }
        return std::nullopt;
    }
    if (node.kind == Kind::Neg && node.children.size() == 1) {
        if (auto v = tryAsConstNumeric(node.children[0])) return -(*v);
    }
    return std::nullopt;
}

ExprId UnconditionalConstantPropagation::substituteRec(ExprId root) {
    if (auto it = substMemo_.find(root); it != substMemo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms (e.g. insertion_sort / large QF_LRA, where this pass
    // runs before any theory). Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (substMemo_.find(e) != substMemo_.end()) { stack.pop_back(); continue; }

        // Value copy: materializeConstant()/ir_.add() below relocate exprs_.
        const auto node = ir_.get(e);

        if (!frame.processed) {
            frame.processed = true;

            // Do not substitute under UF applications: the arithmetic value of
            // `x` flowing into `(f x)` would mint a new UFApply ExprId distinct
            // from any `(f c)` literal, hiding the congruence EUF derives from
            // the active `x = c` (cf. uflia_003 / uflia_017). Leaf here.
            if (node.kind == Kind::UFApply) { substMemo_[e] = e; stack.pop_back(); continue; }

            if (node.kind == Kind::Variable) {
                ExprId res = e;
                if (auto* name = std::get_if<std::string>(&node.payload.value)) {
                    auto it = fixedConstMap_.find(*name);
                    if (it != fixedConstMap_.end()) res = materializeConstant(it->second, node.sort);
                }
                substMemo_[e] = res; stack.pop_back(); continue;
            }

            if (node.children.empty()) { substMemo_[e] = e; stack.pop_back(); continue; }

            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (c != NullExpr && substMemo_.find(c) == substMemo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        std::vector<ExprId> newChildren;
        newChildren.reserve(node.children.size());
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = (c == NullExpr) ? NullExpr : substMemo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        if (!changed) {
            substMemo_[e] = e;
        } else {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            for (ExprId c : newChildren) fresh.children.push_back(c);
            fresh.payload = node.payload;
            substMemo_[e] = ir_.add(std::move(fresh));
        }
    }
    return substMemo_.at(root);
}

ExprId UnconditionalConstantPropagation::materializeConstant(
    const mpq_class& value, SortId sort) {
    // Build the canonical cache key so that two materializations of the
    // same numeric value (e.g. one from substitution and one from a
    // pre-existing literal) share the same ExprId. This is what makes
    // the relation-identity fold (`(distinct (f 2) (f 2)) -> false`)
    // actually fire after substitution + arithmetic folding produces
    // duplicate UF arguments.
    std::string key = std::to_string(sort) + "#";
    if (sort == intSortId_ && value.get_den() == 1
        && value.get_num().fits_slong_p()) {
        int64_t iv = static_cast<int64_t>(value.get_num().get_si());
        key += "I:" + std::to_string(iv);
        auto it = constCache_.find(key);
        if (it != constCache_.end()) return it->second;
        CoreExpr fresh;
        fresh.sort = sort;
        fresh.kind = Kind::ConstInt;
        fresh.payload = Payload(iv);
        ExprId id = ir_.add(std::move(fresh));
        constCache_[key] = id;
        return id;
    }
    key += "R:" + value.get_str();
    auto it = constCache_.find(key);
    if (it != constCache_.end()) return it->second;
    CoreExpr fresh;
    fresh.sort = sort;
    fresh.kind = Kind::ConstReal;
    fresh.payload = Payload(value.get_str());
    ExprId id = ir_.add(std::move(fresh));
    constCache_[key] = id;
    return id;
}

void UnconditionalConstantPropagation::commit() {
    ir_.clearAssertions();
    for (const auto& [level, eid] : rewrittenAssertions_) {
        ir_.addAssertion(eid, level);
    }
}

} // namespace zolver
