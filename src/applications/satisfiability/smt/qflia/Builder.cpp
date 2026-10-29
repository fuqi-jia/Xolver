#include "applications/satisfiability/smt/qflia/Builder.h"
#include "applications/satisfiability/smt/common/lia/LiaSolver.h"
#include "search/coordination/TheoryManager.h"

namespace xolver {
void buildLIA(BuildContext& c) {
    auto& registry = *c.registry;
    auto& theoryManager = *c.theoryManager;
    auto lia = std::make_unique<LiaSolver>();
    lia->setRegistry(&registry);
    theoryManager.registerSolver(std::move(lia));
}

} // namespace xolver
