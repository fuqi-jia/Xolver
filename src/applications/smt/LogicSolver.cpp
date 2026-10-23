#include "applications/smt/LogicSolver.h"
#include "ir/NativeFeatures.h"
namespace xolver::applications::smt {
namespace {
enum Feature : unsigned {
    Int = 1,
    Real = 2,
    Bv = 4,
    Fp = 8,
    Str = 16,
    Array = 32,
    Uf = 64,
    Opaque = 128
};
struct Profile {
    std::string_view name;
    unsigned features;
    bool quantified;
};
Profile profile(Logic logic) {
    switch (logic) {
    case Logic::QF_BV:
        return {"QF_BV", Bv, false};
    case Logic::BV:
        return {"BV", Bv, true};
    case Logic::QF_UFBV:
        return {"QF_UFBV", Bv | Uf, false};
    case Logic::QF_ABV:
        return {"QF_ABV", Bv | Array, false};
    case Logic::QF_AUFBV:
        return {"QF_AUFBV", Bv | Array | Uf, false};
    case Logic::QF_FP:
        return {"QF_FP", Bv | Fp | Real, false};
    case Logic::FP:
        return {"FP", Bv | Fp | Real, true};
    case Logic::QF_BVFP:
        return {"QF_BVFP", Bv | Fp | Real, false};
    case Logic::QF_UFBVFP:
        return {"QF_UFBVFP", Bv | Fp | Real | Uf, false};
    case Logic::QF_ABVFP:
        return {"QF_ABVFP", Bv | Fp | Real | Array, false};
    case Logic::QF_S:
        return {"QF_S", Str | Int, false};
    case Logic::QF_SLIA:
        return {"QF_SLIA", Str | Int, false};
    case Logic::Strings:
        return {"Strings", Str | Int, true};
    case Logic::QF_UF:
        return {"QF_UF", Uf | Opaque, false};
    case Logic::QF_AX:
        return {"QF_AX", Array | Opaque, false};
    case Logic::QF_DT:
        return {"QF_DT", Opaque, false};
    case Logic::QF_UFDT:
        return {"QF_UFDT", Uf | Opaque, false};
    case Logic::QF_BOOL:
        return {"QF_BOOL", 0, false};
    case Logic::QBF:
        return {"QBF", 0, true};
    case Logic::QF_LIA:
        return {"QF_LIA", Int, false};
    case Logic::LIA:
        return {"LIA", Int, true};
    case Logic::QF_LRA:
        return {"QF_LRA", Real, false};
    case Logic::QF_NIA:
        return {"QF_NIA", Int, false};
    case Logic::QF_NRA:
        return {"QF_NRA", Real, false};
    case Logic::NRA:
        return {"NRA", Real, true};
    case Logic::Sequences:
        return {"Sequences", Opaque | Int | Bv, true};
    case Logic::Sets:
        return {"Sets", Opaque | Int | Real, true};
    case Logic::Bags:
        return {"Bags", Opaque | Int | Real, true};
    }
    return {"unknown", 0, false};
}
} // namespace
std::string_view logicName(Logic logic) noexcept { return profile(logic).name; }
SolverAnswer solveLogic(Logic logic, const Problem &p, Solver::GroundSolve ground) {
    const auto spec = profile(logic);
    const auto f = nativeFeatures(p.assertions);
    const unsigned used = (f.integerVariable ? Int : 0) | (f.real ? Real : 0) |
                          (f.bitvector ? Bv : 0) | (f.floatingPoint ? Fp : 0) |
                          (f.strings ? Str : 0) | (f.arrays ? Array : 0) | (f.function ? Uf : 0) |
                          (f.otherSort && !f.floatingPoint && !f.strings && !f.arrays ? Opaque : 0);
    if ((f.quantified && !spec.quantified) || (used & ~spec.features)) {
        SolverAnswer answer;
        answer.reason = "input is outside the selected logic signature";
        return answer;
    }
    return Solver(std::move(ground)).solve(p);
}
} // namespace xolver::applications::smt
