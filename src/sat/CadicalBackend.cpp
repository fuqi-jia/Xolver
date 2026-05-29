#include "sat/CadicalBackend.h"
#include "sat/CadicalTheoryPropagator.h"

namespace xolver {

CadicalBackend::CadicalBackend() : solver_(std::make_unique<CaDiCaL::Solver>()) {
    // Note: we do NOT set factor=0 here.  The state-aware newVar() below
    // handles the SOLVING-state issue; disabling BVA globally hurts SAT
    // search performance and caused NRA regression failures.
}
CadicalBackend::~CadicalBackend() = default;

SatVar CadicalBackend::newVar() {
    if (inSolving_) {
        // Inside a SAT solve() call (e.g. theory-propagator callback).
        // declare_more_variables() requires READY state and will fatal here.
        // Instead we allocate a fresh variable index and immediately mark it
        // observed so CaDiCaL's external-propagator machinery knows about it.
        int v = static_cast<int>(maxVar_);
        int cadicalVars = solver_->vars();
        if (cadicalVars > v) v = cadicalVars;
        ++v;
        maxVar_ = static_cast<SatVar>(v);

        if (propagatorConnected_) {
            solver_->add_observed_var(v);
            if (static_cast<size_t>(v) >= observedVars_.size()) {
                observedVars_.resize(v + 1, false);
            }
            observedVars_[v] = true;
        }
        return maxVar_;
    }

    ++maxVar_;
    if (maxVar_ > declaredVars_) {
        declaredVars_ = maxVar_ + 10000;
        solver_->declare_more_variables(declaredVars_);
    }

    // If an external propagator is already connected (pre-solve setup),
    // observe the variable immediately so it is safe to use in lemmas.
    if (propagatorConnected_) {
        solver_->add_observed_var(static_cast<int>(maxVar_));
        if (maxVar_ >= observedVars_.size()) {
            size_t newSize = std::max(static_cast<size_t>(maxVar_) + 1,
                                      observedVars_.size() * 2);
            newSize = std::max(newSize, static_cast<size_t>(declaredVars_) + 1);
            observedVars_.resize(newSize, false);
        }
        observedVars_[maxVar_] = true;
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
    inSolving_ = true;
    int res = solver_->solve();
    inSolving_ = false;

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

bool CadicalBackend::limit(const char* name, int value) {
    return solver_->limit(name, value);
}

void CadicalBackend::addObservedVar(SatVar v) {
    if (static_cast<size_t>(v) >= observedVars_.size()) {
        size_t newSize = std::max(static_cast<size_t>(v) + 1,
                                  observedVars_.size() * 2);
        newSize = std::max(newSize, static_cast<size_t>(declaredVars_) + 1);
        observedVars_.resize(newSize, false);
    }
    if (!observedVars_[v]) {
        solver_->add_observed_var(static_cast<int>(v));
        observedVars_[v] = true;
    }
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
    observedVars_.clear();
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

} // namespace xolver
