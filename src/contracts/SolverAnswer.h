#pragma once
#include "contracts/Model.h"
#include "xolver/Proof.h"
#include "xolver/Result.h"
#include <optional>
#include <string>

namespace xolver {
// A result protocol shared by solver applications, not an expression IR.
struct SolverAnswer {
    Result result = Result::Unknown;
    std::string reason;
    std::optional<TheoryModel> model;
    Proof proof;
};
} // namespace xolver
