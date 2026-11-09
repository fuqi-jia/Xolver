#include "search/linear/LinearAtomManager.h"
#include <algorithm>

namespace xolver {

bool LinearAtomManager::extractLinearConstraint(ExprId eid, const NativeTerms& ir,
                                                 std::unordered_map<std::string, mpq_class>& coeffs,
                                                 mpq_class& rhs, Relation& rel) const {
    return xolver::extractLinearConstraint(eid, ir, coeffs, rhs, rel);
}

int LinearAtomManager::getOrCreateVar(GeneralSimplex& gs, const std::string& name) {
    auto it = varToIndex_.find(name);
    if (it != varToIndex_.end()) return it->second;
    int idx = gs.addVar(name);
    varToIndex_[name] = idx;
    indexToVar_[idx] = name;  // iter-104 perf: reverse mirror
    return idx;
}

std::string LinearAtomManager::getVarName(int idx) const {
    // iter-104 perf: O(1) reverse lookup. Was O(N) linear scan, called from
    // LIA/LRA hot loops per simplex variable.
    auto it = indexToVar_.find(idx);
    if (it != indexToVar_.end()) return it->second;
    return "";
}

int LinearAtomManager::findVarIndex(const std::string& name) const {
    auto it = varToIndex_.find(name);
    return it != varToIndex_.end() ? it->second : -1;
}

std::optional<bool> LinearAtomManager::evaluateAtModel(
    const GeneralSimplex& gs, const LinearAtomPayload& atom, SortKind domain) const {
    if (domain != SortKind::Int && domain != SortKind::Real) return std::nullopt;
    if (!atom.rhs.isRational()) return std::nullopt;
    DeltaRational value;
    for (const auto& [name, coefficient] : atom.lhs.terms) {
        const int index = findVarIndex(name);
        if (index < 0 || index >= gs.numVars()) return std::nullopt;
        const auto coordinate = gs.value(index);
        if (domain == SortKind::Int && (coordinate.b != 0 || coordinate.a.get_den() != 1)) return std::nullopt;
        value += coefficient * coordinate;
    }
    const DeltaRational rhs(atom.rhs.asRational());
    switch (atom.rel) {
        case Relation::Eq: return value == rhs;
        case Relation::Neq: return value != rhs;
        case Relation::Lt: return value < rhs;
        case Relation::Leq: return value <= rhs;
        case Relation::Gt: return value > rhs;
        case Relation::Geq: return value >= rhs;
    }
    return std::nullopt;
}

bool LinearAtomManager::relationHolds(const DeltaRational& difference, Relation relation) {
    static const DeltaRational zero;
    switch (relation) {
        case Relation::Eq: return difference == zero;
        case Relation::Neq: return difference != zero;
        case Relation::Lt: return difference < zero;
        case Relation::Leq: return difference <= zero;
        case Relation::Gt: return difference > zero;
        case Relation::Geq: return difference >= zero;
    }
    return false;
}

int LinearAtomManager::getOrCreateAuxVar(GeneralSimplex& gs,
                                          const LinearFormKey& lhs,
                                          const mpq_class& rhs) {
    // Borrow the lookup input; only a genuinely new auxiliary column needs an
    // owned copy of the form and its GMP coefficients.
    auto it = formToAux_.find(FormKeyView{lhs, rhs});
    if (it != formToAux_.end()) {
        return it->second;
    }

    FormKey key{lhs, rhs};
    // Build GeneralSimplex terms: (varIndex, coeff)
    std::vector<std::pair<int, mpq_class>> gsTerms;
    gsTerms.reserve(lhs.terms.size());
    for (const auto& [name, coeff] : lhs.terms) {
        int v = getOrCreateVar(gs, name);
        gsTerms.push_back({v, coeff});
    }

    int auxVar = gs.addConstraint(gsTerms, rhs);
    formToAux_[key] = auxVar;
    auxToForm_[auxVar] = key;
    return auxVar;
}

bool LinearAtomManager::auxForm(int aux, LinearFormKey& lhsOut, mpq_class& rhsOut) const {
    auto it = auxToForm_.find(aux);
    if (it == auxToForm_.end()) return false;
    lhsOut = it->second.lhs;
    rhsOut = it->second.rhs;
    return true;
}

LinearAtomManager::RelationBoundViews LinearAtomManager::effectiveBoundViews(
    Relation rel, bool value, bool integerForm) {
    static const DeltaRational zero(0), minusOne(-1), plusOne(1);
    static const DeltaRational strictUpper(0, -1), strictLower(0, 1);
    const auto effective = value ? rel : xolver::negateRelation(rel);
    switch (effective) {
        case Relation::Eq: return {&zero, &zero};
        case Relation::Leq: return {nullptr, &zero};
        case Relation::Lt: return {nullptr, integerForm ? &minusOne : &strictUpper};
        case Relation::Geq: return {&zero, nullptr};
        case Relation::Gt: return {integerForm ? &plusOne : &strictLower, nullptr};
        case Relation::Neq: return {};
    }
    return {};
}

LinearAtomManager::RelationBounds LinearAtomManager::effectiveBounds(
    Relation rel, bool value, bool integerForm) {
    const auto views = effectiveBoundViews(rel, value, integerForm);
    RelationBounds bounds;
    if (views.lower) bounds.lower = *views.lower;
    if (views.upper) bounds.upper = *views.upper;
    return bounds;
}

bool LinearAtomManager::assertBound(GeneralSimplex& gs, int auxVar, Relation rel,
                                    bool value, SatLit reasonLit, int level,
                                    bool integerForm) {
    const auto bounds = effectiveBoundViews(rel, value, integerForm);
    if (bounds.lower && !gs.assertLower(auxVar, BoundInfo(BoundValue(*bounds.lower), reasonLit), level))
        return false;
    return !bounds.upper || gs.assertUpper(auxVar, BoundInfo(BoundValue(*bounds.upper), reasonLit), level);
}

TheoryConflict LinearAtomManager::translateConflict(const GeneralSimplex& gs) const {
    TheoryConflict tc;
    for (const auto& br : gs.getConflict()) {
        // Return the raw asserted SAT literal (true in the current model).
        // TheoryManager is the single place that negates raw reasons into
        // a falsified external conflict clause.
        tc.clause.push_back(br.reason);
    }
    return tc;
}

} // namespace xolver
