#include "search/linear/LinearModelValidator.h"
#include "search/linear/LinearAtomManager.h"

namespace xolver {

bool LinearModelValidator::validateLiaModel(
    const std::vector<ActiveLinearAtom>& activeAtoms,
    const std::vector<DiseqValidationInfo>& disequalities,
    const std::unordered_set<int>& integerVars,
    const GeneralSimplex& gs, const LinearAtomManager& manager) {

    // 1. Check integer variables have integer values
    for (int v : integerVars) {
        auto val = gs.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            return false;
        }
    }

    // 2. Check disequality obligations
    for (const auto& d : disequalities) {
        auto val = gs.value(d.auxVar);
        if (val.isZero()) {
            return false;
        }
    }

    // 3. Check active atoms
    for (const auto& atom : activeAtoms) {
        if (!checkAtom(atom, gs, manager)) {
            return false;
        }
    }

    return true;
}

bool LinearModelValidator::checkAtom(
    const ActiveLinearAtom& atom, const GeneralSimplex& gs,
    const LinearAtomManager& manager) {
    // Recompute the constraint value INDEPENDENTLY from the original form:
    //   val = Σ coeff·value(var) − rhs   ( == aux by construction; lhs rel rhs <=> val rel 0 )
    // Don't trust gs.value(atom.auxVar): if the aux row were ever stale/desynced
    // a violated model would pass. Recomputing from atom.lhs/atom.rhs makes the
    // validator an independent check.
    DeltaRational val;  // 0
    for (const auto& [name, coeff] : atom.lhs.terms) {
        if (coeff == 0) continue;
        const int index = manager.findVarIndex(name);
        if (index < 0 || index >= gs.numVars()) return false;
        val += coeff * gs.value(index);
    }
    val -= DeltaRational(atom.rhs);
    return satisfiesRelation(val, atom.rel, atom.value);
}

bool LinearModelValidator::satisfiesRelation(
    const DeltaRational& val, Relation rel, bool value) {
    // For value=true: check original relation against 0
    // For value=false: check negated relation against 0
    //
    // Original:        Negated:
    //   Eq:  val==0     Neq: val!=0
    //   Lt:  val<0      Geq: val>=0
    //   Leq: val<=0     Gt:  val>0
    //   Gt:  val>0      Leq: val<=0
    //   Geq: val>=0     Lt:  val<0
    //   Neq: val!=0     Eq:  val==0

    if (!value) {
        switch (rel) {
            case Relation::Eq:  rel = Relation::Neq; break;
            case Relation::Lt:  rel = Relation::Geq; break;
            case Relation::Leq: rel = Relation::Gt;  break;
            case Relation::Gt:  rel = Relation::Leq; break;
            case Relation::Geq: rel = Relation::Lt;  break;
            case Relation::Neq: rel = Relation::Eq;  break;
        }
    }

    switch (rel) {
        case Relation::Eq:  return val.isZero();
        case Relation::Neq: return !val.isZero();
        case Relation::Lt:  return val < DeltaRational(0);
        case Relation::Leq: return val <= DeltaRational(0);
        case Relation::Gt:  return val > DeltaRational(0);
        case Relation::Geq: return val >= DeltaRational(0);
    }
    return false;
}

} // namespace xolver
