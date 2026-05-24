#include "frontend/preprocess/ArithCastNormalizer.h"
#include "util/MpqUtils.h"
#include <gmpxx.h>

namespace nlcolver {

CastNormalizeResult ArithCastNormalizer::run() {
    CastNormalizeResult result;
    for (const auto& [level, a] : ir_.getScopedAssertions()) {
        result.assertions.push_back({level, rewriteRec(a)});
    }
    return result;
}

ExprId ArithCastNormalizer::rewriteRec(ExprId root) {
    // Fast path: already memoized
    auto memoIt = memo_.find(root);
    if (memoIt != memo_.end()) return memoIt->second;

    // Iterative DFS to avoid stack overflow on deeply nested chains
    struct Frame {
        ExprId e;
        bool processed;  // false = first visit, true = children done
    };
    std::vector<Frame> stack;
    stack.reserve(64);
    stack.push_back({root, false});

    while (!stack.empty()) {
        Frame& frame = stack.back();
        ExprId e = frame.e;

        // If already memoized, pop and continue
        if (memo_.find(e) != memo_.end()) {
            stack.pop_back();
            continue;
        }

        if (!frame.processed) {
            // First visit: mark as processed, then push children
            frame.processed = true;

            const auto& node = ir_.get(e);

            // Fast path: to_int(to_real(Int)) chain — just jump to inner
            if (node.kind == Kind::ToInt && node.children.size() == 1) {
                const auto& arg = ir_.get(node.children[0]);
                if (arg.kind == Kind::ToReal && arg.children.size() == 1) {
                    const auto& inner = ir_.get(arg.children[0]);
                    if (inner.sort == ir_.intSortId()) {
                        // to_int(to_real(x)) -> x, but x may need rewriting too
                        ExprId innerId = arg.children[0];
                        if (memo_.find(innerId) != memo_.end()) {
                            memo_[e] = memo_[innerId];
                            stack.pop_back();
                            continue;
                        }
                        // Replace current frame with inner node
                        frame.e = innerId;
                        frame.processed = false;
                        continue;
                    }
                }
            }

            // Try constant folding on first visit
            bool folded = false;
            if (node.kind == Kind::ToReal && node.children.size() == 1) {
                const auto& arg = ir_.get(node.children[0]);
                if (arg.kind == Kind::ConstInt) {
                    if (auto* v = std::get_if<int64_t>(&arg.payload.value)) {
                        CoreExpr ne;
                        ne.kind = Kind::ConstReal;
                        ne.sort = node.sort;
                        ne.payload = Payload(mpq_class(*v).get_str());
                        memo_[e] = ir_.add(std::move(ne));
                        folded = true;
                    }
                }
            } else if (node.kind == Kind::ToInt && node.children.size() == 1) {
                const auto& arg = ir_.get(node.children[0]);
                if (arg.kind == Kind::ConstReal) {
                    if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                        mpq_class q = mpqFromString(*s);
                        mpz_class z = q.get_num() / q.get_den();
                        if (q < 0 && q.get_num() % q.get_den() != 0) z -= 1;
                        if (z.fits_slong_p()) {
                            CoreExpr ne;
                            ne.kind = Kind::ConstInt;
                            ne.sort = node.sort;
                            ne.payload = Payload(static_cast<int64_t>(z.get_si()));
                            memo_[e] = ir_.add(std::move(ne));
                            folded = true;
                        }
                    }
                }
            }

            if (folded) {
                stack.pop_back();
                continue;
            }

            // Push children (right-to-left so left is processed first)
            if (!node.children.empty()) {
                for (int i = static_cast<int>(node.children.size()) - 1; i >= 0; --i) {
                    ExprId c = node.children[i];
                    if (memo_.find(c) == memo_.end()) {
                        stack.push_back({c, false});
                    }
                }
            } else {
                // Leaf node
                memo_[e] = e;
                stack.pop_back();
            }
        } else {
            // Second visit: all children are memoized, build result
            const auto& node = ir_.get(e);
            ExprId result = e;

            // Check to_int(to_real(Int)) again (child may have changed)
            if (node.kind == Kind::ToInt && node.children.size() == 1) {
                const auto& arg = ir_.get(node.children[0]);
                if (arg.kind == Kind::ToReal && arg.children.size() == 1) {
                    const auto& inner = ir_.get(arg.children[0]);
                    if (inner.sort == ir_.intSortId()) {
                        auto it = memo_.find(arg.children[0]);
                        if (it != memo_.end()) {
                            memo_[e] = it->second;
                            stack.pop_back();
                            continue;
                        }
                    }
                }
            }

            if (!node.children.empty()) {
                SmallVector<ExprId, 4> newChildren;
                bool changed = false;

                // Detect Real context for integer-constant coercion.
                // For Eq/Distinct/comparisons: if any sibling is Real, coerce Int constants.
                // For arithmetic ops: if parent sort is Real, coerce Int constants.
                bool realContext = false;
                if (ir_.realSortId() != NullSort) {
                    realContext = (node.sort == ir_.realSortId());
                    if (!realContext && (node.kind == Kind::Eq || node.kind == Kind::Distinct ||
                                         node.kind == Kind::Lt || node.kind == Kind::Leq ||
                                         node.kind == Kind::Gt || node.kind == Kind::Geq)) {
                        for (ExprId sib : node.children) {
                            if (ir_.get(sib).sort == ir_.realSortId()) {
                                realContext = true;
                                break;
                            }
                        }
                    }
                }

                for (ExprId c : node.children) {
                    auto it = memo_.find(c);
                    ExprId rc = (it != memo_.end()) ? it->second : c;

                    // Coerce integer constant to real when in a Real context
                    const auto& childNode = ir_.get(c);
                    if (realContext && childNode.kind == Kind::ConstInt) {
                        if (auto* v = std::get_if<int64_t>(&childNode.payload.value)) {
                            CoreExpr ne;
                            ne.kind = Kind::ConstReal;
                            ne.sort = ir_.realSortId();
                            ne.payload = Payload(mpq_class(*v).get_str());
                            rc = ir_.add(std::move(ne));
                            changed = true;
                        }
                    } else if (realContext && childNode.kind == Kind::ConstReal &&
                               childNode.sort == ir_.intSortId()) {
                        // ConstReal node that was classified as Int (e.g. IntOrReal parser constant)
                        if (auto* s = std::get_if<std::string>(&childNode.payload.value)) {
                            CoreExpr ne;
                            ne.kind = Kind::ConstReal;
                            ne.sort = ir_.realSortId();
                            ne.payload = Payload(*s);
                            rc = ir_.add(std::move(ne));
                            changed = true;
                        }
                    }

                    newChildren.push_back(rc);
                    if (rc != c) changed = true;
                }
                if (changed) {
                    CoreExpr ne;
                    ne.kind = node.kind;
                    ne.sort = node.sort;
                    ne.children = std::move(newChildren);
                    ne.payload = node.payload;
                    result = ir_.add(std::move(ne));
                }
            }

            memo_[e] = result;
            stack.pop_back();
        }
    }

    auto it = memo_.find(root);
    return (it != memo_.end()) ? it->second : root;
}

} // namespace nlcolver
