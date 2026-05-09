#include "sat/SatSolver.h"

#ifdef NLCOLVER_HAS_CADICAL

#include <cadical.hpp>
#include <memory>

namespace nlcolver {

/**
 * CadicalBackend: production SAT solver wrapper.
 */
class CadicalBackend : public SatSolver {
public:
    CadicalBackend() : solver_(std::make_unique<CaDiCaL::Solver>()) {}

    SatVar newVar() override {
        solver_->declare_more_variables(1);
        return ++maxVar_;
    }

    void addClause(const std::vector<SatLit>& clause) override {
        for (SatLit lit : clause) {
            int cadicalLit = lit.sign ? static_cast<int>(lit.var)
                                       : -static_cast<int>(lit.var);
            solver_->add(cadicalLit);
        }
        solver_->add(0); // clause terminator
    }

    SolveResult solve() override {
        int res = solver_->solve();
        if (res == CaDiCaL::SATISFIABLE) return SolveResult::Sat;
        if (res == CaDiCaL::UNSATISFIABLE) return SolveResult::Unsat;
        return SolveResult::Unknown;
    }

    SolveResult solve(const std::vector<SatLit>& assumptions) override {
        for (SatLit lit : assumptions) {
            int cadicalLit = lit.sign ? static_cast<int>(lit.var)
                                       : -static_cast<int>(lit.var);
            solver_->assume(cadicalLit);
        }
        return solve();
    }

    bool value(SatVar v) const override {
        return solver_->val(static_cast<int>(v)) > 0;
    }

    bool configure(const char* name, int64_t value) override {
        return solver_->set(name, static_cast<int>(value));
    }

private:
    std::unique_ptr<CaDiCaL::Solver> solver_;
    SatVar maxVar_ = 0;
};

std::unique_ptr<SatSolver> createSatSolver() {
    return std::make_unique<CadicalBackend>();
}

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
