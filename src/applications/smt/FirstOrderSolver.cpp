#include "applications/smt/FirstOrderSolver.h"
#include "applications/smt/lia/Solver.h"
#include "logic/first_order/Solver.h"

namespace xolver::applications::smt {
namespace {
class IntegerBackend final : public logic::first_order::Backend {
    pa::Limits limits;
    pa::EvidenceRequest evidence;
public:
    IntegerBackend(pa::Limits l, pa::EvidenceRequest e) : limits(l), evidence(e) {}
    bool accepts(const logic::first_order::Roots&, const NativeFeatures& f) const override {
        return !f.spatial && !f.function && !f.otherSort && !f.real;
    }
    SolverAnswer solve(const logic::first_order::Roots& roots) override {
        return lia::solve(roots, limits, evidence);
    }
};
}
SolverAnswer solveFirstOrder(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& roots,
                       pa::Limits limits, pa::EvidenceRequest evidence) {
    IntegerBackend integer(limits, evidence);
    logic::first_order::Backend* backends[] = {&integer};
    return logic::first_order::solve(roots, backends);
}
} // namespace xolver::applications::smt
