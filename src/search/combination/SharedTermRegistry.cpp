#include "ir/NumericLiteral.h"
#include "search/combination/SharedTermRegistry.h"
#include "ir/NativeTerms.h"
#include "base/MpqUtils.h"

namespace xolver {

SharedTermId SharedTermRegistry::getOrCreate(ExprId expr, SortId sort,
                                              const std::string& name,
                                              bool isInternal) {
    auto it = exprToId_.find(expr);
    if (it != exprToId_.end()) return it->second;

    // Numeric-constant dedup by value: ConstReal("1") and ConstInt(1) denote
    // the same value, so they must be the same shared term. Otherwise the
    // combination layer can assert a disequality between two equal constants
    // (e.g. 1 != 1), producing a spurious conflict / false UNSAT.
    if (nativeTerms_) {
        if (auto v = numericLiteral(*nativeTerms_, expr)) {
            auto cit = constValueToId_.find(*v);
            if (cit != constValueToId_.end()) {
                exprToId_[expr] = cit->second;  // alias this expr to the canonical term
                return cit->second;
            }
            SharedTermId id = static_cast<SharedTermId>(terms_.size());
            terms_.push_back({id, expr, sort, name, isInternal, {}});
            exprToId_[expr] = id;
            constValueToId_[*v] = id;
            return id;
        }
    }

    SharedTermId id = static_cast<SharedTermId>(terms_.size());
    terms_.push_back({id, expr, sort, name, isInternal, {}});
    exprToId_[expr] = id;
    return id;
}

void SharedTermRegistry::addOwner(SharedTermId id, TheoryId theory) {
    if (id < terms_.size()) {
        terms_[id].owners.insert(theory);
    }
}

const SharedTerm* SharedTermRegistry::get(SharedTermId id) const {
    if (id < terms_.size()) return &terms_[id];
    return nullptr;
}

std::vector<SharedTermId> SharedTermRegistry::termsOwnedBy(TheoryId theory) const {
    std::vector<SharedTermId> out;
    for (const auto& t : terms_) {
        if (t.owners.count(theory)) out.push_back(t.id);
    }
    return out;
}

std::vector<SharedTermId> SharedTermRegistry::allSharedTerms() const {
    std::vector<SharedTermId> out;
    out.reserve(terms_.size());
    for (const auto& t : terms_) out.push_back(t.id);
    return out;
}

std::vector<SharedTermId> SharedTermRegistry::sharedTermsOfSort(SortId sort) const {
    std::vector<SharedTermId> out;
    for (const auto& t : terms_) {
        if (t.sort == sort) out.push_back(t.id);
    }
    return out;
}

bool SharedTermRegistry::hasTerm(ExprId expr) const {
    return exprToId_.count(expr);
}

std::optional<SharedTermId> SharedTermRegistry::findByExprId(ExprId expr) const {
    auto it = exprToId_.find(expr);
    if (it != exprToId_.end()) return it->second;
    return std::nullopt;
}

std::optional<mpq_class> SharedTermRegistry::constValue(SharedTermId id) const {
    if (!nativeTerms_ || id >= terms_.size()) return std::nullopt;
    return numericLiteral(*nativeTerms_, terms_[id].nativeExpr);
}

void SharedTermRegistry::clear() {
    terms_.clear();
    exprToId_.clear();
    constValueToId_.clear();
}

} // namespace xolver
