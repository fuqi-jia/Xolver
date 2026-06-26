#include "theory/arith/kernel/linear/LinearModelValidator.h"

namespace xolver {

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

    // Build a name->simplex-index map once, so each atom can be re-evaluated
    // from its ORIGINAL linear form rather than trusting its aux-var row.
    std::unordered_map<std::string, int> nameToIdx;
    nameToIdx.reserve(static_cast<size_t>(gs.numVars()));
    for (int v = 0; v < gs.numVars(); ++v) {
        nameToIdx.emplace(gs.varName(v), v);
    }

    // 3. Check active atoms
    for (const auto& atom : activeAtoms) {
        if (!checkAtom(atom, gs, nameToIdx)) {
            return false;
        }
    }

    return true;
}

bool LinearModelValidator::checkAtom(
    const ActiveLinearAtom& atom, const GeneralSimplex& gs,
    const std::unordered_map<std::string, int>& nameToIdx) {
    // Recompute the constraint value INDEPENDENTLY from the original form:
    //   val = Σ coeff·value(var) − rhs   ( == aux by construction; lhs rel rhs <=> val rel 0 )
    // Don't trust gs.value(atom.auxVar): if the aux row were ever stale/desynced
    // a violated model would pass. Recomputing from atom.lhs/atom.rhs makes the
    // validator an independent check.
    DeltaRational val;  // 0
    bool allResolved = true;
    for (const auto& [name, coeff] : atom.lhs.terms) {
        auto it = nameToIdx.find(name);
        if (it == nameToIdx.end()) { allResolved = false; break; }
        val += coeff * gs.value(it->second);
    }
    if (allResolved) {
        val -= DeltaRational(atom.rhs);
        return satisfiesRelation(val, atom.rel, atom.value);
    }
    // Fallback (a form var not registered in the simplex — should not happen for
    // an asserted atom): preserve the prior aux-var behavior.
    return satisfiesRelation(gs.value(atom.auxVar), atom.rel, atom.value);
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
