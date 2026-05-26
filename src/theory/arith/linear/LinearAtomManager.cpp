#include "theory/arith/linear/LinearAtomManager.h"
#include <algorithm>

namespace zolver {

bool LinearAtomManager::extractLinearConstraint(ExprId eid, const CoreIr& ir,
                                                 std::unordered_map<std::string, mpq_class>& coeffs,
                                                 mpq_class& rhs, Relation& rel) const {
    return zolver::extractLinearConstraint(eid, ir, coeffs, rhs, rel);
}

int LinearAtomManager::getOrCreateVar(GeneralSimplex& gs, const std::string& name) {
    auto it = varToIndex_.find(name);
    if (it != varToIndex_.end()) return it->second;
    int idx = gs.addVar(name);
    varToIndex_[name] = idx;
    return idx;
}

std::string LinearAtomManager::getVarName(int idx) const {
    for (const auto& [name, id] : varToIndex_) {
        if (id == idx) return name;
    }
    return "";
}

int LinearAtomManager::findVarIndex(const std::string& name) const {
    auto it = varToIndex_.find(name);
    return it != varToIndex_.end() ? it->second : -1;
}

int LinearAtomManager::getOrCreateAuxVar(GeneralSimplex& gs,
                                          const LinearFormKey& lhs,
                                          const mpq_class& rhs) {
    FormKey key{lhs, rhs};
    auto it = formToAux_.find(key);
    if (it != formToAux_.end()) {
        return it->second;
    }

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

bool LinearAtomManager::assertBound(GeneralSimplex& gs, int auxVar, Relation rel,
                                    bool value, SatLit reasonLit, int level) {
    Relation effective = value ? rel : zolver::negateRelation(rel);

    bool ok = true;
    switch (effective) {
        case Relation::Eq:
            ok = gs.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit), level);
            if (!ok) break;
            ok = gs.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit), level);
            break;
        case Relation::Leq:
            ok = gs.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit), level) && ok;
            break;
        case Relation::Lt:
            ok = gs.assertUpper(auxVar, BoundInfo(BoundValue(DeltaRational(0, -1)), reasonLit), level) && ok;
            break;
        case Relation::Geq:
            ok = gs.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit), level) && ok;
            break;
        case Relation::Gt:
            ok = gs.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0, 1)), reasonLit), level) && ok;
            break;
        case Relation::Neq:
            // Neq cannot be expressed as a single convex bound.
            // The caller (LraSolver/LiaSolver) must handle disequalities separately.
            break;
    }
    return ok;
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

} // namespace zolver
