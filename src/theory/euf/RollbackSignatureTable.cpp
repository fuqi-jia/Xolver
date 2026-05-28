#include "theory/euf/RollbackSignatureTable.h"

namespace xolver {

std::optional<EufTermId> RollbackSignatureTable::find(const AppSignature& sig) const {
    auto it = table_.find(sig);
    if (it == table_.end()) return std::nullopt;
    return it->second;
}

void RollbackSignatureTable::insertOrAssign(const AppSignature& sig, EufTermId owner) {
    auto it = table_.find(sig);
    if (it == table_.end()) {
        trail_.push_back({ChangeKind::InsertNew, sig, std::nullopt});
        table_.emplace(sig, owner);
        return;
    }
    if (it->second == owner) {
        return;
    }
    trail_.push_back({ChangeKind::Overwrite, sig, it->second});
    it->second = owner;
}

void RollbackSignatureTable::eraseIfOwner(const AppSignature& sig, EufTermId owner) {
    auto it = table_.find(sig);
    if (it == table_.end()) return;
    if (it->second != owner) return;
    trail_.push_back({ChangeKind::Erase, sig, it->second});
    table_.erase(it);
}

size_t RollbackSignatureTable::snapshot() const {
    return trail_.size();
}

void RollbackSignatureTable::rollback(size_t snap) {
    while (trail_.size() > snap) {
        auto ch = trail_.back();
        trail_.pop_back();
        switch (ch.kind) {
            case ChangeKind::InsertNew:
                table_.erase(ch.sig);
                break;
            case ChangeKind::Overwrite:
                table_[ch.sig] = *ch.previousOwner;
                break;
            case ChangeKind::Erase:
                table_[ch.sig] = *ch.previousOwner;
                break;
        }
    }
}

void RollbackSignatureTable::clear() {
    table_.clear();
    trail_.clear();
}

} // namespace xolver
