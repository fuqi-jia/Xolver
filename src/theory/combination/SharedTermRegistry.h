#pragma once
#include "expr/types.h"
#include <vector>
#include <string>
#include <optional>
#include <unordered_map>
#include <unordered_set>

namespace nlcolver {

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

    void clear();

private:
    std::vector<SharedTerm> terms_;
    std::unordered_map<ExprId, SharedTermId> exprToId_;
};

} // namespace nlcolver
