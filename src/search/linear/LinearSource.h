#pragma once

#include "contracts/AffineFormKey.h"
#include "contracts/TheoryAtomTypes.h"

namespace xolver {

// A source owns its current SAT premises and shares only immutable mathematics.
// Copies and scope snapshots keep their definitions alive independently.
struct LinearSource {
    int level;
    SatLit lit;
    SatVar satVar;
    ExprId exprId;
    Relation relation;
    bool value;
    int auxVar;
    bool isDiseq;
    AffineFormDefinition form;

    const LinearFormKey& lhs() const { return form->lhs; }
    const mpq_class& rhs() const { return form->rhs; }

    bool matches(const TheoryAtomRecord& atom, const LinearAtomPayload& payload,
                 const mpq_class& rhsValue, bool assignedValue,
                 int assignedLevel, SatLit assignedLit) const {
        return satVar == atom.satVar && level == assignedLevel && lit == assignedLit &&
            exprId == atom.exprId && value == assignedValue && relation == payload.rel &&
            AffineFormKeyEqual{}(*form, AffineFormKeyView{payload.lhs, rhsValue});
    }

    struct Key {
        SatVar operator()(const LinearSource& source) const { return source.satVar; }
    };
};

} // namespace xolver
