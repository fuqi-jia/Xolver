#include "experimental/mcsat/MCSatTrail.h"

namespace xolver {
namespace mcsat {

bool MCSatTrail::indexBool_(SatLit lit, size_t idx) {
    auto [it, inserted] = boolIndex_.emplace(lit.var, idx);
    (void)it;
    return inserted;
}

bool MCSatTrail::indexVar_(VarId v, size_t idx) {
    auto [it, inserted] = varIndex_.emplace(v, idx);
    (void)it;
    return inserted;
}

void MCSatTrail::unindexEntry_(const TrailEntry& e) {
    switch (e.kind) {
        case TrailEntryKind::BoolDecision:
        case TrailEntryKind::BoolPropagation:
            boolIndex_.erase(e.lit.var);
            break;
        case TrailEntryKind::TheoryDecision:
        case TrailEntryKind::TheoryPropagation:
            varIndex_.erase(e.var);
            break;
    }
}

bool MCSatTrail::pushBoolDecision(SatLit lit, int level) {
    if (boolIndex_.count(lit.var)) return false;
    entries_.push_back({TrailEntryKind::BoolDecision, level, lit, NullVar, RealValue{}, {}});
    indexBool_(lit, entries_.size() - 1);
    return true;
}

bool MCSatTrail::pushBoolPropagation(SatLit lit, int level,
                                     std::vector<SatLit> reasons) {
    if (boolIndex_.count(lit.var)) return false;
    entries_.push_back({TrailEntryKind::BoolPropagation, level, lit,
                        NullVar, RealValue{}, std::move(reasons)});
    indexBool_(lit, entries_.size() - 1);
    return true;
}

bool MCSatTrail::pushTheoryDecision(VarId var, RealValue value, int level) {
    if (var == NullVar) return false;
    if (varIndex_.count(var)) return false;
    entries_.push_back({TrailEntryKind::TheoryDecision, level, SatLit{},
                        var, std::move(value), {}});
    indexVar_(var, entries_.size() - 1);
    return true;
}

bool MCSatTrail::pushTheoryPropagation(VarId var, RealValue value, int level,
                                       std::vector<SatLit> reasons) {
    if (var == NullVar) return false;
    if (varIndex_.count(var)) return false;
    entries_.push_back({TrailEntryKind::TheoryPropagation, level, SatLit{},
                        var, std::move(value), std::move(reasons)});
    indexVar_(var, entries_.size() - 1);
    return true;
}

void MCSatTrail::backtrackToLevel(int targetLevel) {
    while (!entries_.empty() && entries_.back().level > targetLevel) {
        unindexEntry_(entries_.back());
        entries_.pop_back();
    }
}

void MCSatTrail::clear() {
    entries_.clear();
    boolIndex_.clear();
    varIndex_.clear();
}

std::optional<bool> MCSatTrail::lookupBool(SatVar v) const {
    auto it = boolIndex_.find(v);
    if (it == boolIndex_.end()) return std::nullopt;
    return entries_[it->second].lit.sign;
}

const RealValue* MCSatTrail::lookupVar(VarId v) const {
    auto it = varIndex_.find(v);
    if (it == varIndex_.end()) return nullptr;
    return &entries_[it->second].value;
}

int MCSatTrail::topLevel() const {
    if (entries_.empty()) return 0;
    return entries_.back().level;
}

} // namespace mcsat
} // namespace xolver
