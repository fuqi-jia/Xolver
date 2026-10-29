#pragma once
#include "applications/dynamics/Solver.h"
namespace xolver::applications::dynamics::ode {
class Solver final : public dynamics::Solver {
  public:
    explicit Solver(Options options = {}) : dynamics::Solver(Kind::Ode, options) {}
};
} // namespace xolver::applications::dynamics::ode
