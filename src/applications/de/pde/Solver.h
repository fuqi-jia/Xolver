#pragma once
#include "applications/de/Solver.h"
namespace xolver::applications::de::pde {
class Solver final : public de::Solver {
  public:
    explicit Solver(Options options = {}) : de::Solver(Kind::Pde, options) {}
};
} // namespace xolver::applications::de::pde
