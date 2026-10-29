#pragma once
#include "applications/dynamics/Solver.h"
namespace xolver::applications::dynamics::pde {
class Solver final : public dynamics::Solver {
  public:
    explicit Solver(Options options = {}) : dynamics::Solver(Kind::Pde, options) {}
};
} // namespace xolver::applications::dynamics::pde
