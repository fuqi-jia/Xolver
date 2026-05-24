#include "theory/arith/ArithSolverBase.h"

namespace nlcolver {

void ArithSolverBase::push() {
    ++state_.scopeLevel;
    onPush();
}

void ArithSolverBase::pop(uint32_t n) {
    if (state_.scopeLevel >= n) state_.scopeLevel -= n;
    else state_.scopeLevel = 0;
    onPop(n);
}

void ArithSolverBase::assertLit(const TheoryAtomRecord& atom, bool value,
                                int level, SatLit assertedLit) {
    // Dedup by satVar: replace an existing assignment for the same SAT
    // variable in place, else append. This reproduces the pre-refactor
    // assertLit body shared by IDL/RDL/NIA/NIRA/LIRA verbatim.
    for (auto& a : state_.trail) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            if (level > state_.currentLevel) state_.currentLevel = level;
            onAssertLit(atom, value, level, assertedLit);
            return;
        }
    }
    state_.trail.push_back({level, assertedLit, atom, value});
    if (level > state_.currentLevel) state_.currentLevel = level;
    onAssertLit(atom, value, level, assertedLit);
}

void ArithSolverBase::backtrackToLevel(int level) {
    auto it = std::remove_if(state_.trail.begin(), state_.trail.end(),
        [level](const ActiveAssignment& a) { return a.level > level; });
    state_.trail.erase(it, state_.trail.end());

    if (state_.pending && state_.pending->level > level) {
        state_.pending.reset();
    }
    state_.currentLevel = level;
    onBacktrack(level);
}

void ArithSolverBase::reset() {
    state_.trail.clear();
    state_.pending.reset();
    state_.currentLevel = 0;
    state_.scopeLevel = 0;
    onReset();
}

} // namespace nlcolver
