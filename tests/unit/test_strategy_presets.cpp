#include <doctest/doctest.h>
#include "frontend/factory/StrategyPresets.h"
#include "zolver/Solver.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>

using namespace zolver;

TEST_CASE("strategy presets: Phase-1 invariants") {
    LogicFeatures f;
    for (const char* logic : {"QF_LIA", "QF_NIA", "QF_NRA", "QF_LRA", "QF_UF",
                              "QF_AX", "QF_UFLIA", "QF_LIRA", "QF_IDL", ""}) {
        StrategyConfig c = selectStrategy(logic, f);
        // Phase 1: rewriter is the enabled knob...
        CHECK(c.enableRewrite);
        // ...LIA flags stay at engine defaults (behavior-neutral)...
        CHECK_FALSE(c.liaSafeMode);
        CHECK_FALSE(c.liaUltraSafeMode);
        CHECK_FALSE(c.liaEnableSingleVar);
        CHECK_FALSE(c.liaEnableGcdIneq);
        CHECK_FALSE(c.liaEnableEqGcdNorm);
        // ...and no cross-agent env flags are enabled (those branches are not
        // merged/validated here). Empty envFlags => no setenv => no leakage.
        CHECK(c.envFlags.empty());
    }
}

TEST_CASE("strategy presets: ZOLVER_STRAT_PRESETS drives rewriter end-to-end") {
    struct EnvGuard {
        EnvGuard()  { setenv("ZOLVER_STRAT_PRESETS", "1", 1); }
        ~EnvGuard() { unsetenv("ZOLVER_STRAT_PRESETS"); }
    } guard;

    // The preset enables the rewriter; the deep EUF chain that exposed the
    // use-after-realloc must stay unsat through this path too.
    std::string smt =
        "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n"
        "(declare-const x U)(declare-const y U)\n(assert (= x y))\n"
        "(assert (distinct (f (f (f (f (f x))))) (f (f (f (f (f y)))))))\n(check-sat)\n";
    std::string path = (std::filesystem::temp_directory_path() /
                        "zolver_strat_euf.smt2").string();
    { std::ofstream(path) << smt; }

    Solver solver;
    REQUIRE(solver.parseFile(path));
    Result r = solver.checkSat();
    CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
}
