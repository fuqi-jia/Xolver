#include "theory/arith/linear/LinearAtomManager.h"
#include <algorithm>

namespace xolver {

bool LinearAtomManager::extractLinearConstraint(ExprId eid, const CoreIr& ir,
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
                                    bool value, SatLit reasonLit, int level,
                                    bool integerForm) {
    Relation effective = value ? rel : xolver::negateRelation(rel);

    // Integer strict tightening: for an integer-valued aux s, s < 0 <=> s <= -1
    // and s > 0 <=> s >= 1 (exact — no integer lies in the open gap). This
    // replaces the δ-strict bound that branch-and-bound cannot close on an
    // integer-empty range like n < d < n+1, where it would otherwise chase the
    // real-feasible relaxation forever.
    const DeltaRational strictUpper = integerForm ? DeltaRational(-1) : DeltaRational(0, -1);
    const DeltaRational strictLower = integerForm ? DeltaRational(1)  : DeltaRational(0, 1);

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
            ok = gs.assertUpper(auxVar, BoundInfo(BoundValue(strictUpper), reasonLit), level) && ok;
            break;
        case Relation::Geq:
            ok = gs.assertLower(auxVar, BoundInfo(BoundValue(DeltaRational(0)), reasonLit), level) && ok;
            break;
        case Relation::Gt:
            ok = gs.assertLower(auxVar, BoundInfo(BoundValue(strictLower), reasonLit), level) && ok;
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

} // namespace xolver
