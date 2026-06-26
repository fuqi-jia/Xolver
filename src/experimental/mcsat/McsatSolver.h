#pragma once

// McsatSolver — generic MCSAT framework, implemented as a TheorySolver.
//
// MCSAT (Model-Constructing SAT) interleaves Boolean and theory-variable
// assignments on a single trail. The framework here owns the trail,
// scope/level tracking, and the main decide/propagate/conflict loop;
// algebraic decisions are delegated to an MCSatEngine subclass:
//
//   NRA (real values, libpoly cells)   → src/theory/arith/logics/nra/engine/NlsatEngine
//   NIA (integer values, modular etc.) → src/theory/arith/logics/nia/mcsat/NiaMcsatEngine
//
// Soundness floor (mirrors docs/agents/NLSAT-plan.md §15):
//   - A theory-decision value is never reported as a SAT literal.
//   - check() never returns Sat without engine_->validateModel() succeeding.
//   - check() returns Conflict only when explainConflict() produced a
//     theory-valid clause.

#include "experimental/mcsat/MCSatEngine.h"
#include "experimental/mcsat/MCSatTrail.h"
#include "experimental/search/LocalSearchAdvisor.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include "theory/core/TheorySolver.h"
#include <memory>

namespace xolver {

class McsatSolver : public TheorySolver {
public:
    McsatSolver();
    ~McsatSolver() override;

    // The framework reports the engine's theory id; default is NRA so the
    // existing skeleton wiring still compiles. Concrete engines override
    // this via setEngine().
    TheoryId id() const override { return theoryId_; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtomRecord& atom, bool value,
                   int level, SatLit reason) override;
    void backtrackToLevel(int level) override;
    TheoryCheckResult check(TheoryLemmaStorage& lemmaDb,
                            TheoryEffort effort = TheoryEffort::Standard) override;
    void reset() override;

    // Plug in the per-theory engine (NRA or NIA). Must be called before any
    // assertLit. Takes ownership.
    void setEngine(std::unique_ptr<mcsat::MCSatEngine> engine, TheoryId tid);

    // Optional kernel ownership: TheoryFactory hands us the polynomial
    // kernel as a unique_ptr (mirroring the existing NraSolver/NiaSolver
    // pattern). The kernel pointer the engine borrowed must outlive the
    // engine; owning it here keeps that invariant after registerSolver.
    void setKernel(std::unique_ptr<PolynomialKernel> kernel) {
        ownedKernel_ = std::move(kernel);
    }
    PolynomialKernel* kernel() const { return ownedKernel_.get(); }

    // Legacy advisor wiring (kept so existing code compiles); unused by the
    // generic framework.
    void setAdvisor(std::shared_ptr<LocalSearchAdvisor> advisor);

    // Test/diagnostic accessor.
    const mcsat::MCSatTrail& trail() const { return trail_; }

private:
    // Run one full decide-loop iteration: pick a variable, ask the engine
    // for a feasible value, push the decision onto the trail. Returns true
    // iff a decision was made. False either means "all variables decided"
    // (engine returned NullVar) or "engine returned ValueChoice{ok=false}",
    // in which case the conflict has already been queued via
    // pendingConflict_.
    bool tryDecideOnce_();

    mcsat::MCSatTrail trail_;
    std::unique_ptr<mcsat::MCSatEngine> engine_;
    TheoryId theoryId_ = TheoryId::NRA;

    // Tracks the framework-side decision level (incremented on push,
    // decremented on pop). assertLit uses this when forwarding to the
    // engine and when pushing entries onto the trail.
    int currentLevel_ = 0;

    // When a conflict was discovered out-of-band (e.g. during pickValue),
    // it parks here so the next check() can return it without losing the
    // explanation.
    std::optional<TheoryConflict> pendingConflict_;

    // When the engine signaled GiveUp, the framework parks an Unknown
    // verdict here. Never turned into UNSAT.
    std::optional<std::string> pendingGiveUp_;

    // Legacy advisor (unused).
    std::shared_ptr<LocalSearchAdvisor> advisor_;

    // Kernel ownership (when handed in by TheoryFactory). Optional —
    // some test fixtures construct the McsatSolver with a borrowed
    // kernel that the test owns directly.
    std::unique_ptr<PolynomialKernel> ownedKernel_;
    // Limitation-(b) AlgebraBackend ownership. TheoryFactory hands an
    // owning unique_ptr<AlgebraBackend> here so its lifetime is tied to
    // the solver. The engine borrows a raw pointer via setAlgebra. The
    // setter body is out-of-line (in McsatSolver.cpp) so callers that
    // never touch AlgebraBackend.h don't pay an include cost.
    std::unique_ptr<class AlgebraBackend> ownedAlgebra_;
public:
    void setAlgebra(std::unique_ptr<class AlgebraBackend> algebra);
    class AlgebraBackend* algebra() const { return ownedAlgebra_.get(); }
};

} // namespace xolver
