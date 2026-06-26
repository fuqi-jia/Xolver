#define DOCTEST_CONFIG_IMPLEMENT
#include <doctest/doctest.h>
#include <cstdlib>

// The CLI bakes competition-default flags (xolverBakeCompetitionDefaults in
// tools/cli/main.cpp); the bare Solver API used by the unit/e2e tests otherwise
// runs a NON-shipped configuration. Combination soundness fixes — e.g. the #77
// derived-argument UF-over-arith congruence (f(0) < f((-1)+j) with j pinned to
// 1) — rely on the model-based scalar arrangement + backfill, which are
// competition defaults. Bake the combination group here so the e2e regression
// tests validate the SHIPPED behaviour. setenv(...,/*overwrite=*/0) does NOT
// clobber a per-test override (e.g. test_model_based_arrangement toggles
// XOLVER_COMB_MODEL_BASED itself with overwrite=1 / unsetenv), so scoped tests
// still win.
int main(int argc, char** argv) {
    const char* kCombFlags[] = {
        "XOLVER_COMB_MODEL_BASED", "XOLVER_COMB_SCALAR_BACKFILL",
        "XOLVER_COMB_UFARG_ARRANGE", "XOLVER_UF_FAST_CC",
    };
    for (const char* f : kCombFlags) setenv(f, "1", /*overwrite=*/0);
    return doctest::Context(argc, argv).run();
}
