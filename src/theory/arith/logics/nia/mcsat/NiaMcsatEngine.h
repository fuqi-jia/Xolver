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
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <memory>
#include <unordered_set>
#include <vector>

namespace xolver {

class CdcacCore;          // real-relaxation refutation (nra/core)
class LibpolyBackend;     // libpoly algebra backend (nra/backend)
class TheoryAtomRegistry; // mints the integrality-split bound atoms

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
    void setRegistry(TheoryAtomRegistry* reg) { registry_ = reg; }

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
    std::vector<TheoryLemma> takeLemmas() override;
    bool validateModel(const mcsat::MCSatTrail& trail,
                       TheorySolver::TheoryModel& outModel) override;

private:
    std::unordered_set<VarId> collectVariables_() const;

    PolynomialKernel* kernel_ = nullptr;
    const class CoreIr* coreIr_ = nullptr;
    TheoryAtomRegistry* registry_ = nullptr;

    std::vector<AssertedAtom> asserted_;
    // Integrality split lemmas produced in pickValue, drained by takeLemmas().
    std::vector<TheoryLemma> pendingLemmas_;

    mutable std::vector<VarId> varOrderCache_;
    mutable bool varOrderCacheValid_ = false;

    // Limitation-(c) integer DFS: same shape as the NRA engine's
    // DFS-driven complete-assignment search but restricted to integer
    // candidates. Cleared on assertLit/onBacktrack/reset.
    std::unordered_map<VarId, RealValue> cachedAssignment_;
    bool cachedAssignmentTried_ = false;
    bool cachedAssignmentSucceeded_ = false;

    // Integer reinforcement (§15.5 real-relaxation UNSAT): when no integer model
    // is found, run CDCAC on the REAL relaxation of the asserted atoms; a real
    // empty-covering proof (CdcacStatus::Unsat, already projection-certified)
    // implies integer UNSAT (ℤⁿ⊆ℝⁿ). Lazily constructed; conflict clause is
    // stashed in pendingExplainClause_ for explainConflict.
    std::unique_ptr<LibpolyBackend> algebra_;
    std::unique_ptr<CdcacCore> cdcacFallback_;
    std::vector<SatLit> pendingExplainClause_;
    bool realRelaxTried_ = false;
    // Per-solve budget on integrality splits — a backstop so a wiring gap (a
    // bound atom not reaching the real-relaxation) degrades to Unknown, never an
    // infinite split loop. Reset only on reset() (must persist across branches).
    int integralitySplitBudget_ = 5000;
};

} // namespace nia_mcsat
} // namespace xolver
