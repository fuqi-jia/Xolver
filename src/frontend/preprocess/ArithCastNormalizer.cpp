#include "frontend/preprocess/ArithCastNormalizer.h"
#include <gmpxx.h>

namespace nlcolver {

CastNormalizeResult ArithCastNormalizer::run() {
    CastNormalizeResult result;
    for (const auto& [level, a] : ir_.getScopedAssertions()) {
        result.assertions.push_back({level, rewriteRec(a)});
    }
    return result;
}

ExprId ArithCastNormalizer::rewriteRec(ExprId e) {
    auto it = memo_.find(e);
    if (it != memo_.end()) return it->second;

    const auto& node = ir_.get(e);
    ExprId result = e;

    if (node.kind == Kind::ToReal && node.children.size() == 1) {
        const auto& arg = ir_.get(node.children[0]);
        if (arg.kind == Kind::ConstInt) {
            if (auto* v = std::get_if<int64_t>(&arg.payload.value)) {
                CoreExpr ne;
                ne.kind = Kind::ConstReal;
                ne.sort = node.sort;
                ne.payload = Payload(mpq_class(*v).get_str());
                result = ir_.add(std::move(ne));
            }
        }
    } else if (node.kind == Kind::ToInt && node.children.size() == 1) {
        const auto& arg = ir_.get(node.children[0]);
        if (arg.kind == Kind::ConstReal) {
            if (auto* s = std::get_if<std::string>(&arg.payload.value)) {
                mpq_class q(*s);
                mpz_class z = q.get_num() / q.get_den();
                if (q < 0 && q.get_num() % q.get_den() != 0) z -= 1;
                // Only fold if the result fits in int64_t
                if (z.fits_slong_p()) {
                    CoreExpr ne;
                    ne.kind = Kind::ConstInt;
                    ne.sort = node.sort;
                    ne.payload = Payload(static_cast<int64_t>(z.get_si()));
                    result = ir_.add(std::move(ne));
                }
            }
        } else if (arg.kind == Kind::ToReal && arg.children.size() == 1) {
            const auto& inner = ir_.get(arg.children[0]);
            if (inner.sort == ir_.intSortId()) {
                result = rewriteRec(arg.children[0]); // to_int(to_real(IntTerm)) -> IntTerm
            }
        }
    }

    if (result == e && !node.children.empty()) {
        SmallVector<ExprId, 4> newChildren;
        bool changed = false;
        for (ExprId c : node.children) {
            ExprId rc = rewriteRec(c);
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
    return result;
}

} // namespace nlcolver
