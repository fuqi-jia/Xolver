#pragma once
#include "expr/types.h"
#include <vector>
#include <string>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <gmpxx.h>

namespace zolver {

class CoreIr;

struct SharedTerm {
    SharedTermId id;
    ExprId coreExpr;      // original CoreIr expression
    SortId sort;
    std::string name;     // for debugging
    bool isInternal;      // true if created by Purifier
    std::unordered_set<TheoryId> owners;
};

class SharedTermRegistry {
public:
    SharedTermRegistry() = default;

    // Optional CoreIr, used to dedup numeric-constant shared terms by value so
    // that e.g. ConstReal("1") and ConstInt(1) map to a single shared term
    // (they are the same value; EUF interns them identically, and treating them
    // as distinct shared terms produces spurious interface (dis)equalities).
    void setCoreIr(const CoreIr* ir) { coreIr_ = ir; }
    const CoreIr* coreIr() const { return coreIr_; }

    // Get or create a shared term for an expression.
    // If the expression is already registered, return existing id.
    SharedTermId getOrCreate(ExprId expr, SortId sort,
                             const std::string& name,
                             bool isInternal);

    void addOwner(SharedTermId id, TheoryId theory);

    const SharedTerm* get(SharedTermId id) const;

    std::vector<SharedTermId> termsOwnedBy(TheoryId theory) const;
    std::vector<SharedTermId> allSharedTerms() const;
    std::vector<SharedTermId> sharedTermsOfSort(SortId sort) const;

    bool hasTerm(ExprId expr) const;
    std::optional<SharedTermId> findByExprId(ExprId expr) const;

    // Numeric (Int/Real) constant value of a shared term, if it is one. Used
    // by the combination layer to refute an interface equality asserted between
    // two distinct numeric constants (e.g. the array Row2 split picking
    // (1 = 2)), which no arith solver constrains when neither side is a
    // simplex variable. Requires setCoreIr() to have been called.
    std::optional<mpq_class> constValue(SharedTermId id) const;

    void clear();

private:
    std::vector<SharedTerm> terms_;
    std::unordered_map<ExprId, SharedTermId> exprToId_;
    const CoreIr* coreIr_ = nullptr;
    std::map<mpq_class, SharedTermId> constValueToId_;  // numeric-constant dedup by value
};

} // namespace zolver
