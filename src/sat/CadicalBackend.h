#pragma once

#include "sat/SatSolver.h"
#include <cadical.hpp>
#include <memory>

namespace xolver {

class CadicalTheoryPropagator;

class CadicalBackend : public SatSolver {
public:
    CadicalBackend();
    ~CadicalBackend() override;

    SatVar newVar() override;
    void addClause(const std::vector<SatLit>& clause) override;
    SolveResult solve() override;
    SolveResult solve(const std::vector<SatLit>& assumptions) override;
    bool value(SatVar v) const override;
    bool configure(const char* name, int64_t value) override;
    bool limit(const char* name, int value) override;
    std::vector<SatLit> getFailedAssumptions() const override;
    void addObservedVar(SatVar v) override;

    void connectPropagator(CadicalTheoryPropagator* propagator);
    void disconnectPropagator();
    void requestTerminate();

    // Statistics (available only when compiled with CaDiCaL)
    struct Stats {
        int64_t vars = 0;
        int64_t clauses = 0;
        int64_t conflicts = 0;
        int64_t decisions = 0;
        int64_t propagations = 0;
    };
    Stats getStats() const;

private:
    // Wall-clock terminator: CaDiCaL polls terminate() DURING solve(), so even a
    // single long internal SAT solve (e.g. the bit-blast's dedicated solver, whose
    // conflict limit is unbounded by default) aborts when the solve deadline
    // passes. Default-INERT: terminate() is false unless XOLVER_WALLCLOCK_MS set a
    // deadline that has now passed (wall::remainingMs()). Sound: an aborted solve
    // returns Unknown.
    struct WallClockTerminator : public CaDiCaL::Terminator {
        bool terminate() override;
    };
    WallClockTerminator wallTerm_;

    std::unique_ptr<CaDiCaL::Solver> solver_;
    SatVar maxVar_ = 0;
    SatVar declaredVars_ = 0;
    bool terminateRequested_ = false;
    bool propagatorConnected_ = false;
    bool inSolving_ = false;
    std::vector<SatLit> lastAssumptions_;
    std::vector<bool> observedVars_;
};

} // namespace xolver
