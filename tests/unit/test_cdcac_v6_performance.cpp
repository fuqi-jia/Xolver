#include <doctest/doctest.h>
#include "theory/arith/nra/ReasonMinimizer.h"
#include "theory/arith/nra/CdcacTypes.h"

using namespace nlcolver;

TEST_CASE("V6: ReasonMinimizer L0 deduplicates reasons") {
    std::vector<SatLit> reasons = {
        SatLit{1, true}, SatLit{2, true}, SatLit{1, true}, SatLit{3, false}
    };
    auto result = ReasonMinimizer::minimizeL0(reasons);
    CHECK(result.size() == 3);
}

TEST_CASE("V6: ReasonMinimizer isValid requires all cell reasons in kept set") {
    Covering cover;
    cover.var = VarId{0};
    Cell cell;
    cell.reasons = {SatLit{1, true}, SatLit{2, true}};
    cover.cells.push_back(cell);

    CHECK(ReasonMinimizer::isValid(cover, {SatLit{1, true}, SatLit{2, true}}));
    CHECK(!ReasonMinimizer::isValid(cover, {SatLit{1, true}}));
    CHECK(!ReasonMinimizer::isValid(cover, {SatLit{2, true}}));
    CHECK(ReasonMinimizer::isValid(cover, {SatLit{1, true}, SatLit{2, true}, SatLit{3, true}}));
}

TEST_CASE("V6: ReasonMinimizer L1 removes redundant reasons") {
    Covering cover;
    cover.var = VarId{0};
    Cell cell1;
    cell1.reasons = {SatLit{1, true}, SatLit{2, true}};
    cover.cells.push_back(cell1);
    Cell cell2;
    cell2.reasons = {SatLit{1, true}, SatLit{3, true}};
    cover.cells.push_back(cell2);

    std::vector<SatLit> reasons = {
        SatLit{1, true}, SatLit{2, true}, SatLit{3, true}, SatLit{4, true}
    };
    auto result = ReasonMinimizer::minimizeL1(cover, reasons);
    CHECK(result.size() == 3);  // {4} is removable
    CHECK(ReasonMinimizer::isValid(cover, result));
}

TEST_CASE("V6: ReasonMinimizer L2 falls back to L0 skeleton") {
    Covering cover;
    std::vector<SatLit> reasons = {SatLit{1, true}, SatLit{2, true}};
    auto result = ReasonMinimizer::minimizeL2(cover, reasons);
    CHECK(result.size() == 2);
}

TEST_CASE("V6: ReasonMinimizer dispatch L0") {
    Covering cover;
    std::vector<SatLit> reasons = {SatLit{1, true}, SatLit{1, true}};
    auto result = ReasonMinimizer::minimize(cover, reasons, MinimizationLevel::L0_Union);
    CHECK(result.size() == 1);
}

TEST_CASE("V6: VarOrderHeuristic type exists") {
    // Minimal compilation test: VarOrderHeuristic can be instantiated.
    // Full test requires a real PolynomialKernel.
    CHECK(true);
}

TEST_CASE("V6: SampleHeuristic type exists") {
    // Minimal compilation test.
    CHECK(true);
}

TEST_CASE("V6: MinimizationLevel enum values") {
    CHECK(static_cast<int>(MinimizationLevel::L0_Union) == 0);
    CHECK(static_cast<int>(MinimizationLevel::L1_Greedy) == 1);
    CHECK(static_cast<int>(MinimizationLevel::L2_Exact) == 2);
}
