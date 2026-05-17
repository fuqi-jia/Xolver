#pragma once

#include "sat/SatSolver.h"

#ifdef NLCOLVER_HAS_CADICAL

#include <cadical.hpp>
#include <memory>

namespace nlcolver {

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
    std::vector<SatLit> getFailedAssumptions() const override;
    void addObservedVar(SatVar v) override;

    void connectPropagator(CadicalTheoryPropagator* propagator);
    void disconnectPropagator();
    void requestTerminate();

private:
    std::unique_ptr<CaDiCaL::Solver> solver_;
    SatVar maxVar_ = 0;
    bool terminateRequested_ = false;
    bool propagatorConnected_ = false;
    std::vector<SatLit> lastAssumptions_;
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
