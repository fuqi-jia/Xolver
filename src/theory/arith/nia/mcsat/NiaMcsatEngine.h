#pragma once

// NiaMcsatEngine — NIA backend for the MCSAT framework.
//
// NIA over MCSAT differs from NRA in three ways:
//   1. Variables carry integer sort: value choices must be integers
//      (mpz_class wrapped in RealValue::fromMpz). Algebraic values are
//      never used here.
//   2. Conflict explanation must respect §15.4 (Real SAT ≠ Int SAT):
//      if a value falls in the real-relaxation feasible set but is not
//      an integer, the engine emits an integrality lemma
//      (x ≤ floor(α) ∨ x ≥ ceil(α)) rather than claiming SAT.
//   3. The §15.5 sound-UNSAT-source list applies. UNSAT-shape clauses
//      may come from real-relaxation UNSAT, modular exhaustion, gcd
//      infeasibility, bounded bit-blast, or branch-and-bound closure
//      — never from heuristic failure.
//
// This engine reuses the existing NIA reasoners (ModularResidueReasoner,
// BoundedNiaSolver, IntegerModelValidator) for theory-side soundness gates.
// The first wake delivers stubs; subsequent wakes fill in the algebra.

#include "experimental/mcsat/MCSatEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <memory>
#include <unordered_set>
#include <vector>

namespace xolver {
namespace nia_mcsat {

struct AssertedAtom {
    TheoryAtomRecord atom;
    bool value = true;
    int level = 0;
    SatLit assertedLit{};
};

class NiaMcsatEngine : public mcsat::MCSatEngine {
public:
    NiaMcsatEngine();
    ~NiaMcsatEngine() override;

    void setKernel(PolynomialKernel* kernel) { kernel_ = kernel; }
    void setCoreIr(const class CoreIr* coreIr) { coreIr_ = coreIr; }

    // MCSatEngine API
    void reset() override;
    void onAssertAtom(const TheoryAtomRecord& atom, bool value, int level,
                      SatLit assertedLit) override;
    void onBacktrack(int targetLevel) override;
    VarId pickNextVar(const mcsat::MCSatTrail& trail) override;
    mcsat::ValueChoice pickValue(VarId var,
                                 const mcsat::MCSatTrail& trail) override;
    std::vector<SatLit> explainConflict(
        const mcsat::MCSatTrail& trail,
        const std::vector<TheoryAtomRecord>& blockingAtoms) override;
    bool validateModel(const mcsat::MCSatTrail& trail,
                       TheorySolver::TheoryModel& outModel) override;

private:
    std::unordered_set<VarId> collectVariables_() const;

    PolynomialKernel* kernel_ = nullptr;
    const class CoreIr* coreIr_ = nullptr;

    std::vector<AssertedAtom> asserted_;

    mutable std::vector<VarId> varOrderCache_;
    mutable bool varOrderCacheValid_ = false;

    // Limitation-(c) integer DFS: same shape as the NRA engine's
    // DFS-driven complete-assignment search but restricted to integer
    // candidates. Cleared on assertLit/onBacktrack/reset.
    std::unordered_map<VarId, RealValue> cachedAssignment_;
    bool cachedAssignmentTried_ = false;
    bool cachedAssignmentSucceeded_ = false;
};

} // namespace nia_mcsat
} // namespace xolver
