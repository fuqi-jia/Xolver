#pragma once
#include "applications/de/Solver.h"
namespace xolver::applications::de::ode {
class Solver final : public de::Solver {
  public:
    explicit Solver(Options options = {}) : de::Solver(Kind::Ode, options) {}
};
} // namespace xolver::applications::de::ode
