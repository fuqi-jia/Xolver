#include "search/arith/LinearDifferenceEqualityIndex.h"
#include "algebra/linear/LinearExpr.h"
#include <algorithm>
#include <string_view>
#include <unordered_map>

namespace xolver {

void LinearDifferenceEqualityIndex::add(
        const LinearAtomPayload& atom, bool value, SatLit reason) {
    if (!atom.rhs.isRational()) return;
    add(atom.lhs, atom.rel, atom.rhs.asRational(), value, reason);
}

void LinearDifferenceEqualityIndex::add(
        const LinearFormKey& lhs, Relation assertedRelation, const mpq_class& rhs,
        bool value, SatLit reason) {
    if (lhs.terms.size() != 2) return;
    const auto& [name0, coefficient0] = lhs.terms[0];
    const auto& [name1, coefficient1] = lhs.terms[1];
    if (name0 == name1 || coefficient0 == 0 || coefficient0 != -coefficient1) return;
    const Relation relation = value ? assertedRelation : negateRelation(assertedRelation);
    // Strict bounds and disequalities do not pin a real difference to zero.
    if (relation != Relation::Eq && relation != Relation::Leq && relation != Relation::Geq)
        return;
    if (name0 < name1)
        entries_[{name0, name1}].push_back({coefficient0, relation, rhs, reason});
    else
        entries_[{name1, name0}].push_back({coefficient1, relation, rhs, reason});
}

std::vector<LinearDifferenceEqualityIndex::PinnedPair>
LinearDifferenceEqualityIndex::pinnedPairs(std::span<const std::string> sharedNames) const {
    std::vector<PinnedPair> result;
    if (entries_.empty()) return result;
    // Views borrow only this call's input; no model or trail state is retained.
    std::unordered_map<std::string_view, std::vector<size_t>> positions;
    positions.reserve(sharedNames.size());
    for (size_t i = 0; i < sharedNames.size(); ++i)
        if (!sharedNames[i].empty()) positions[sharedNames[i]].push_back(i);

    for (const auto& [names, bounds] : entries_) {
        const auto first = positions.find(names.first);
        const auto second = positions.find(names.second);
        if (first == positions.end() || second == positions.end()) continue;
        bool haveLower = false, haveUpper = false;
        mpq_class lower = 0, upper = 0;
        SatLit lowerReason{}, upperReason{};
        auto addLower = [&](const mpq_class& value, SatLit reason) {
            if (!haveLower || value > lower) {
                lower = value; lowerReason = reason; haveLower = true;
            }
        };
        auto addUpper = [&](const mpq_class& value, SatLit reason) {
            if (!haveUpper || value < upper) {
                upper = value; upperReason = reason; haveUpper = true;
            }
        };
        for (const auto& bound : bounds) {
            const mpq_class value = bound.rhs / bound.coefficient;
            const bool flip = bound.coefficient < 0;
            switch (bound.relation) {
                case Relation::Eq:
                    addLower(value, bound.reason); addUpper(value, bound.reason); break;
                case Relation::Leq:
                    if (flip) addLower(value, bound.reason); else addUpper(value, bound.reason);
                    break;
                case Relation::Geq:
                    if (flip) addUpper(value, bound.reason); else addLower(value, bound.reason);
                    break;
                default: break;
            }
        }
        if (!(haveLower && haveUpper && lower == 0 && upper == 0)) continue;
        for (size_t i : first->second)
            for (size_t j : second->second)
                result.push_back({std::min(i, j), std::max(i, j), lowerReason, upperReason});
    }
    std::sort(result.begin(), result.end(), [](const auto& a, const auto& b) {
        return a.first < b.first || (a.first == b.first && a.second < b.second);
    });
    return result;
}

} // namespace xolver
