#include "applications/sv/pa/Presburger.h"
#include "quantifiers/integer/NativeFormula.h"
#include "ir/NativeFeatures.h"

namespace xolver::pa {
bool hasQuantifiers(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& roots) {
    return nativeFeatures(roots).quantified;
}
Decision decide(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& roots,
                Limits limits, EvidenceRequest evidence) {
    Solver solver(limits, evidence);
    return solver.solve(roots);
}
Decision Solver::solve(const Problem& roots) {
    quantifiers::IntegerFormula compiler(limits, evidence);
    return compiler.decide([&] { return compiler.compile(roots); });
}
} // namespace xolver::pa
