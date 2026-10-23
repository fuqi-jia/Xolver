#pragma once
#include "applications/smt/Solver.h"
namespace xolver::applications::smt {
enum class Logic {
    QF_BV,
    BV,
    QF_UFBV,
    QF_ABV,
    QF_AUFBV,
    QF_FP,
    FP,
    QF_BVFP,
    QF_UFBVFP,
    QF_ABVFP,
    QF_S,
    QF_SLIA,
    Strings,
    QF_UF,
    QF_AX,
    QF_DT,
    QF_UFDT,
    QF_BOOL,
    QBF,
    QF_LIA,
    QF_LRA,
    QF_NIA,
    QF_NRA,
    LIA,
    NRA,
    Sequences,
    Sets,
    Bags
};
std::string_view logicName(Logic) noexcept;
SolverAnswer solveLogic(Logic, const Problem &, Solver::GroundSolve = {});
template <Logic L> class LogicSolver final : public TypedSolver<Problem, SolverAnswer> {
    smt::Solver::GroundSolve ground_;

  public:
    explicit LogicSolver(smt::Solver::GroundSolve ground = {}) : ground_(std::move(ground)) {}
    Family family() const noexcept override { return Family::Smt; }
    std::string_view name() const noexcept override { return logicName(L); }
    SolverAnswer solve(const Problem &p) override { return solveLogic(L, p, ground_); }
};
} // namespace xolver::applications::smt
