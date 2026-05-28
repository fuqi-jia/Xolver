#pragma once

#include "expr/ir.h"
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * CoreIteLowerer: pure IR-to-IR pass that eliminates ExprKind::Ite.
 *
 * Input: CoreIr assertions (may contain Ite nodes).
 * Output: ITE-free assertions + generated definition assertions.
 *
 * Invariants:
 *   - Does NOT create SatLit.
 *   - Does NOT register theory atoms.
 *   - Does NOT call SAT backend.
 *   - Fresh symbols use internal reserved names guaranteed unique.
 *   - Term memo key includes (ExprId, expectedSort) to defend IntOrReal ambiguity.
 */
class CoreIteLowerer {
public:
    explicit CoreIteLowerer(CoreIr& ir);

    // Lower a single assertion.  Generated definitions accumulate in generatedAssertions_.
    ExprId lowerAssertion(ExprId assertion);

    // All ITE definition assertions generated during lowering.
    const std::vector<ExprId>& generatedAssertions() const { return generatedAssertions_; }

private:
    ExprId lowerExpr(ExprId e, SortId expectedSort);
    ExprId lowerBoolExpr(ExprId e);

    ExprId lowerTermIte(ExprId iteExpr, SortId resultSort);
    ExprId lowerBoolIte(ExprId iteExpr);

    ExprId freshTerm(SortId sort);
    ExprId freshBool();

    ExprId rebuildLike(ExprId original, const std::vector<ExprId>& newChildren);

private:
    CoreIr& ir_;
    SortId boolSortId_;

    // Bool expressions: key is just ExprId (Bool sort has no IntOrReal ambiguity).
    std::unordered_map<ExprId, ExprId> boolMemo_;

    // Term expressions: key includes expectedSort to defend IntOrReal ambiguity.
    struct TermKey {
        ExprId expr;
        SortId expectedSort;
        bool operator==(const TermKey& o) const noexcept {
            return expr == o.expr && expectedSort == o.expectedSort;
        }
    };
    struct TermKeyHash {
        size_t operator()(const TermKey& k) const noexcept {
            size_t h1 = std::hash<ExprId>{}(k.expr);
            size_t h2 = std::hash<SortId>{}(k.expectedSort);
            return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
        }
    };
    std::unordered_map<TermKey, ExprId, TermKeyHash> termMemo_;

    std::vector<ExprId> generatedAssertions_;
};

} // namespace xolver
