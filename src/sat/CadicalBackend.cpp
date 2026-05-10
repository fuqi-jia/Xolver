#include "sat/CadicalBackend.h"

#ifdef NLCOLVER_HAS_CADICAL

#include "sat/CadicalTheoryPropagator.h"

namespace nlcolver {

CadicalBackend::CadicalBackend() : solver_(std::make_unique<CaDiCaL::Solver>()) {}
CadicalBackend::~CadicalBackend() = default;

SatVar CadicalBackend::newVar() {
    if (!propagatorConnected_) {
        solver_->declare_more_variables(1);
    }
    return ++maxVar_;
}

void CadicalBackend::addClause(const std::vector<SatLit>& clause) {
    for (SatLit lit : clause) {
        int cadicalLit = lit.sign ? static_cast<int>(lit.var)
                                   : -static_cast<int>(lit.var);
        solver_->add(cadicalLit);
    }
    solver_->add(0);
}

SatSolver::SolveResult CadicalBackend::solve() {
    terminateRequested_ = false;
    int res = solver_->solve();

    if (terminateRequested_) {
        terminateRequested_ = false;
        return SolveResult::Unknown;
    }

    if (res == CaDiCaL::SATISFIABLE) return SolveResult::Sat;
    if (res == CaDiCaL::UNSATISFIABLE) return SolveResult::Unsat;
    return SolveResult::Unknown;
}

SatSolver::SolveResult CadicalBackend::solve(const std::vector<SatLit>& assumptions) {
    for (SatLit lit : assumptions) {
        int cadicalLit = lit.sign ? static_cast<int>(lit.var)
                                   : -static_cast<int>(lit.var);
        solver_->assume(cadicalLit);
    }
    return solve();
}

bool CadicalBackend::value(SatVar v) const {
    return solver_->val(static_cast<int>(v)) > 0;
}

bool CadicalBackend::configure(const char* name, int64_t value) {
    return solver_->set(name, static_cast<int>(value));
}

void CadicalBackend::addObservedVar(SatVar v) {
    solver_->add_observed_var(static_cast<int>(v));
}

void CadicalBackend::connectPropagator(CadicalTheoryPropagator* propagator) {
    solver_->declare_more_variables(1000000);
    solver_->connect_external_propagator(propagator);
    propagatorConnected_ = true;
}

void CadicalBackend::disconnectPropagator() {
    solver_->disconnect_external_propagator();
    propagatorConnected_ = false;
}

void CadicalBackend::requestTerminate() {
    terminateRequested_ = true;
    solver_->terminate();
}

std::unique_ptr<SatSolver> createSatSolver() {
    return std::make_unique<CadicalBackend>();
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
