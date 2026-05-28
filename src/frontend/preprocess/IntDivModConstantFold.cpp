#include "frontend/preprocess/IntDivModConstantFold.h"
#include <gmpxx.h>
#include <optional>

namespace xolver {

IntDivModConstantFold::IntDivModConstantFold(CoreIr& ir)
    : ir_(ir), intSortId_(ir.intSortId()) {}

bool IntDivModConstantFold::run() {
    memo_.clear();
    folded_.clear();
    didFold_ = false;

    for (const auto& [level, eid] : ir_.getScopedAssertions()) {
        ExprId rewritten = foldRec(eid);
        folded_.emplace_back(level, rewritten);
    }
    return true;
}

void IntDivModConstantFold::commit() {
    if (!didFold_) return;
    ir_.clearAssertions();
    for (const auto& [level, eid] : folded_) {
        ir_.addAssertion(eid, level);
    }
}

ExprId IntDivModConstantFold::foldRec(ExprId root) {
    if (auto it = memo_.find(root); it != memo_.end()) return it->second;

    // Iterative post-order (two-visit work-stack) to avoid stack overflow on
    // deeply nested terms. Behavior-identical to the former recursion.
    struct Frame { ExprId e; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;
        if (memo_.find(e) != memo_.end()) { stack.pop_back(); continue; }

        const auto node = ir_.get(e);  // value copy: tryFoldDivMod/ir_.add may relocate

        if (!frame.processed) {
            frame.processed = true;
            if (node.children.empty()) { memo_[e] = e; stack.pop_back(); continue; }
            for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                ExprId c = node.children[i];
                if (memo_.find(c) == memo_.end()) stack.push_back({c, false});
            }
            continue;
        }

        stack.pop_back();
        SmallVector<ExprId, 4> newChildren;
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = memo_.at(c);
            if (rc != c) changed = true;
            newChildren.push_back(rc);
        }
        ExprId rebuilt = e;
        if (changed) {
            CoreExpr fresh;
            fresh.kind = node.kind;
            fresh.sort = node.sort;
            fresh.children = std::move(newChildren);
            fresh.payload = node.payload;
            rebuilt = ir_.add(std::move(fresh));
        }
        // Try div/mod constant fold at the current node.
        ExprId folded = tryFoldDivMod(rebuilt);
        if (folded != rebuilt) didFold_ = true;
        memo_[e] = folded;
    }

    return memo_.at(root);
}

namespace {

std::optional<mpz_class> extractIntConst(const CoreExpr& n) {
    if (n.kind == Kind::ConstInt) {
        if (auto* v = std::get_if<int64_t>(&n.payload.value)) return mpz_class(*v);
        return std::nullopt;
    }
    if (n.kind == Kind::ConstReal) {
        // Defensive: the parser may carry int-valued literals via ConstReal.
        if (auto* s = std::get_if<std::string>(&n.payload.value)) {
            mpq_class q(*s);
            if (q.get_den() == 1) return mpz_class(q.get_num());
        }
        return std::nullopt;
    }
    return std::nullopt;
}

// SMT-LIB integer div/mod (euclidean): given a, b with b != 0,
//   q = sign(b) * floor(a / |b|)   if b > 0:  q = floor(a/b)
//                                    if b < 0:  q = -floor(a/|b|)
//   r = a - b * q,   guaranteed 0 <= r < |b|.
std::pair<mpz_class, mpz_class> smtlibDivMod(const mpz_class& a, const mpz_class& b) {
    mpz_class absB = abs(b);
    // floor division of a by absB, returning q', r' with 0 <= r' < absB.
    mpz_class qAbs;
    mpz_class rAbs;
    mpz_fdiv_qr(qAbs.get_mpz_t(), rAbs.get_mpz_t(), a.get_mpz_t(), absB.get_mpz_t());
    // rAbs in [0, absB)
    mpz_class q = (b > 0) ? qAbs : -qAbs;
    mpz_class r = rAbs;
    return {q, r};
}

} // namespace

ExprId IntDivModConstantFold::tryFoldDivMod(ExprId e) {
    const auto& node = ir_.get(e);
    if (node.sort != intSortId_) return e;
    if (node.kind != Kind::Div && node.kind != Kind::Mod) return e;
    if (node.children.size() != 2) return e;
    auto a = extractIntConst(ir_.get(node.children[0]));
    auto b = extractIntConst(ir_.get(node.children[1]));
    if (!a || !b) return e;
    if (*b == 0) return e;  // leave for IntDivModLowerer's undef branch.

    auto [q, r] = smtlibDivMod(*a, *b);
    const mpz_class& value = (node.kind == Kind::Div) ? q : r;
    if (!value.fits_slong_p()) return e;  // refuse oversized literals.
    return mkConstInt(value.get_si());
}

ExprId IntDivModConstantFold::mkConstInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.add(std::move(e));
}

} // namespace xolver
