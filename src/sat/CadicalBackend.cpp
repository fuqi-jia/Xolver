#include "sat/CadicalBackend.h"

#ifdef NLCOLVER_HAS_CADICAL

#include "sat/CadicalTheoryPropagator.h"

namespace nlcolver {

CadicalBackend::CadicalBackend() : solver_(std::make_unique<CaDiCaL::Solver>()) {}
CadicalBackend::~CadicalBackend() = default;

SatVar CadicalBackend::newVar() {
    ++maxVar_;
    if (maxVar_ > declaredVars_) {
        declaredVars_ = maxVar_ + 10000;
        solver_->declare_more_variables(declaredVars_);
    }
    return maxVar_;
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
    lastAssumptions_ = assumptions;
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

std::vector<SatLit> CadicalBackend::getFailedAssumptions() const {
    std::vector<SatLit> failed;
    for (SatLit lit : lastAssumptions_) {
        int cadicalLit = lit.sign ? static_cast<int>(lit.var)
                                   : -static_cast<int>(lit.var);
        if (solver_->failed(cadicalLit)) {
            failed.push_back(lit);
        }
    }
    return failed;
}

bool CadicalBackend::configure(const char* name, int64_t value) {
    return solver_->set(name, static_cast<int>(value));
}

void CadicalBackend::addObservedVar(SatVar v) {
    solver_->add_observed_var(static_cast<int>(v));
}

void CadicalBackend::connectPropagator(CadicalTheoryPropagator* propagator) {
    if (maxVar_ > declaredVars_) {
        declaredVars_ = maxVar_ + 10000;
        solver_->declare_more_variables(declaredVars_);
    }
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

CadicalBackend::Stats CadicalBackend::getStats() const {
    Stats s;
    s.vars = solver_->active();
    s.clauses = solver_->irredundant() + solver_->redundant();
    s.conflicts = solver_->get("conflicts");
    s.decisions = solver_->get("decisions");
    s.propagations = solver_->get("propagations");
    return s;
}

std::unique_ptr<SatSolver> createSatSolver() {
    return std::make_unique<CadicalBackend>();
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
