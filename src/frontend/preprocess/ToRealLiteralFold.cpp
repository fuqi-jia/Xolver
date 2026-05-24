#include "frontend/preprocess/ToRealLiteralFold.h"
#include <gmpxx.h>

namespace nlcolver {

namespace {

// tryAsConstNumeric: integer or rational-string ConstReal -> mpq.
std::optional<mpq_class> tryAsConstNumeric(const CoreIr& ir, ExprId e) {
    const auto& node = ir.get(e);
    if (node.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&node.payload.value)) {
            return mpq_class(*v);
        }
        return std::nullopt;
    }
    if (node.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&node.payload.value)) {
            try { return mpq_class(*s); } catch (...) { return std::nullopt; }
        }
        return std::nullopt;
    }
    if (node.kind == Kind::Neg && node.children.size() == 1) {
        if (auto v = tryAsConstNumeric(ir, node.children[0])) return -(*v);
    }
    return std::nullopt;
}

} // namespace

ToRealLiteralFold::ToRealLiteralFold(CoreIr& ir)
    : ir_(ir), realSortId_(ir.realSortId()) {}

bool ToRealLiteralFold::run() {
    memo_.clear();
    folded_.clear();
    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        folded_.emplace_back(level, foldRec(eid));
    }
    return true;
}

void ToRealLiteralFold::commit() {
    ir_.clearAssertions();
    for (const auto& [level, e] : folded_) {
        ir_.addAssertion(e, level);
    }
}

ExprId ToRealLiteralFold::foldRec(ExprId e) {
    if (auto it = memo_.find(e); it != memo_.end()) return it->second;
    const auto& node = ir_.get(e);
    if (node.children.empty()) {
        memo_[e] = e;
        return e;
    }

    std::vector<ExprId> newChildren;
    newChildren.reserve(node.children.size());
    bool changed = false;
    for (ExprId c : node.children) {
        ExprId rc = foldRec(c);
        if (rc != c) changed = true;
        newChildren.push_back(rc);
    }

    ExprId rebuilt;
    if (!changed) {
        rebuilt = e;
    } else {
        CoreExpr fresh;
        fresh.kind = node.kind;
        fresh.sort = node.sort;
        for (ExprId c : newChildren) fresh.children.push_back(c);
        fresh.payload = node.payload;
        rebuilt = ir_.add(std::move(fresh));
    }

    // After rebuilding children, try to fold this node itself.
    if (ir_.get(rebuilt).kind == Kind::ToReal) {
        ExprId folded = tryFoldToReal(rebuilt);
        memo_[e] = folded;
        return folded;
    }
    if (ir_.get(rebuilt).kind == Kind::Div
        && ir_.get(rebuilt).sort == realSortId_) {
        ExprId folded = tryFoldDivOfConsts(rebuilt);
        memo_[e] = folded;
        return folded;
    }
    memo_[e] = rebuilt;
    return rebuilt;
}

ExprId ToRealLiteralFold::tryFoldToReal(ExprId node) {
    const auto& n = ir_.get(node);
    if (n.children.size() != 1) return node;
    ExprId arg = n.children[0];
    const auto& argNode = ir_.get(arg);
    if (argNode.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&argNode.payload.value)) {
            return mkConstReal(mpq_class(*v));
        }
    }
    // (to_real ConstReal r) -> already real; just unwrap.
    if (argNode.kind == Kind::ConstReal) {
        return arg;
    }
    return node;
}

ExprId ToRealLiteralFold::tryFoldDivOfConsts(ExprId node) {
    const auto& n = ir_.get(node);
    if (n.children.size() != 2) return node;
    auto aOpt = tryAsConstNumeric(ir_, n.children[0]);
    auto bOpt = tryAsConstNumeric(ir_, n.children[1]);
    if (!aOpt || !bOpt) return node;
    if (*bOpt == 0) return node;            // leave 0-divisor unfolded
    mpq_class result = *aOpt / *bOpt;
    return mkConstReal(result);
}

ExprId ToRealLiteralFold::mkConstReal(const mpq_class& value) {
    CoreExpr fresh;
    fresh.kind = Kind::ConstReal;
    fresh.sort = realSortId_;
    fresh.payload = Payload(value.get_str());
    return ir_.add(std::move(fresh));
}

} // namespace nlcolver
