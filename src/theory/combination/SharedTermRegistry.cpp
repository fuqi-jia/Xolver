#include "theory/combination/SharedTermRegistry.h"

namespace nlcolver {

SharedTermId SharedTermRegistry::getOrCreate(ExprId expr, SortId sort,
                                              const std::string& name,
                                              bool isInternal) {
    auto it = exprToId_.find(expr);
    if (it != exprToId_.end()) return it->second;

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

bool SharedTermRegistry::hasTerm(ExprId expr) const {
    return exprToId_.count(expr);
}

std::optional<SharedTermId> SharedTermRegistry::findByExprId(ExprId expr) const {
    auto it = exprToId_.find(expr);
    if (it != exprToId_.end()) return it->second;
    return std::nullopt;
}

void SharedTermRegistry::clear() {
    terms_.clear();
    exprToId_.clear();
}

} // namespace nlcolver
