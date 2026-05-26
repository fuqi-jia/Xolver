#include "theory/arith/linear/LinearModelValidator.h"

namespace zolver {

bool LinearModelValidator::validateLiaModel(
    const std::vector<ActiveLinearAtom>& activeAtoms,
    const std::vector<DiseqValidationInfo>& disequalities,
    const std::unordered_set<int>& integerVars,
    const GeneralSimplex& gs) {

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
        if (!checkAtom(atom, gs)) {
            return false;
        }
    }

    return true;
}

bool LinearModelValidator::checkAtom(
    const ActiveLinearAtom& atom, const GeneralSimplex& gs) {
    // aux = lhs - rhs, so:
    //   lhs rel rhs  <=>  aux rel 0
    auto val = gs.value(atom.auxVar);
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

} // namespace zolver
