#include <doctest/doctest.h>
#include "search/linear/IntegerModelCompletion.h"
#include "search/lra/GeneralSimplex.h"
#include <chrono>
#include <stdexcept>
#include <vector>

using namespace xolver;

TEST_CASE("integer model completion: repair a fractional vertex without changing affine bounds") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("x"), y = simplex.addVar("y");
    const int sum = simplex.addConstraint({{x, 2}, {y, 1}}, mpq_class(101));
    const auto reason = SatLit::positive(1);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertLower(y, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertLower(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    simplex.push();
    REQUIRE(simplex.assertUpper(y, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    simplex.pop(GeneralSimplex::AssignmentPolicy::Preserve);
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    const std::vector<int> columns{x, y};
    IntegerCompletionStatistics stats;
    const auto model = completeIntegerModel(simplex, columns,
        std::chrono::steady_clock::now() + std::chrono::seconds(1), 64, [] {}, &stats);
    REQUIRE(model.has_value());
    CHECK(model->at(x).get_den() == 1);
    CHECK(model->at(y).get_den() == 1);
    CHECK(2 * model->at(x) + model->at(y) == 101);
    CHECK(model->at(x) >= 0);
    CHECK(model->at(y) >= 0);
    CHECK(stats.fractionalPoints > 0);
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    CHECK(simplex.value(y).a == 101); // repair pins did not leak
    CHECK(simplex.debugCheckInvariants());
}

TEST_CASE("integer model completion: inconclusive search never alters caller levels or conflict") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("x");
    const auto reason = SatLit::positive(9);
    const BoundInfo half(BoundValue(DeltaRational(mpq_class(1, 2))), reason);
    REQUIRE(simplex.assertLower(x, half, 3));
    REQUIRE(simplex.assertUpper(x, half, 3));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    const std::vector<int> columns{x};
    auto run = [&](size_t limit) {
        return completeIntegerModel(simplex, columns,
            std::chrono::steady_clock::now() + std::chrono::seconds(1), limit, [] {});
    };
    CHECK_FALSE(run(64));
    CHECK_FALSE(run(0));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    REQUIRE(simplex.fixedValue(x).has_value());
    CHECK(simplex.fixedValue(x)->a == mpq_class(1, 2));
    CHECK(simplex.getConflict().empty());
    simplex.backtrackToLevel(2, GeneralSimplex::AssignmentPolicy::Preserve);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(7)), reason), 2));
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(7)), reason), 2));
    const auto model = run(64);
    REQUIRE(model.has_value());
    CHECK(model->at(x) == 7);
}

TEST_CASE("integer model completion: cancellation unwinds every local pin") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("x"), y = simplex.addVar("y");
    const int sum = simplex.addConstraint({{x, 2}, {y, 2}}, mpq_class(101));
    const auto reason = SatLit::positive(1);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertLower(y, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertLower(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    const std::vector<int> columns{x, y};
    IntegerCompletionStatistics stats;
    CHECK_THROWS_AS(completeIntegerModel(simplex, columns,
        std::chrono::steady_clock::now() + std::chrono::seconds(1), 64,
        [&] { if (stats.pins) throw std::runtime_error("cancel"); }, &stats), std::runtime_error);
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    CHECK(simplex.value(y).a == mpq_class(101, 2));
    CHECK(simplex.getConflict().empty());
    CHECK(simplex.debugCheckInvariants());
}

TEST_CASE("integer model completion: real columns retain fractions under strict integer bounds") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("integer"), y = simplex.addVar("real");
    const int sum = simplex.addConstraint({{x, 1}, {y, 1}}, mpq_class(3, 2));
    const auto reason = SatLit::positive(1);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(0, 1)), reason)));
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(2, -1)), reason)));
    REQUIRE(simplex.assertLower(y, BoundInfo(BoundValue(DeltaRational(mpq_class(1, 4))), reason)));
    REQUIRE(simplex.assertLower(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    REQUIRE(simplex.assertUpper(sum, BoundInfo(BoundValue(DeltaRational(0)), reason)));
    simplex.push();
    const BoundInfo half(BoundValue(DeltaRational(mpq_class(1, 2))), reason);
    REQUIRE(simplex.assertLower(x, half));
    REQUIRE(simplex.assertUpper(x, half));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    simplex.pop(GeneralSimplex::AssignmentPolicy::Preserve);
    const std::vector<int> integerColumns{x};
    const auto model = completeIntegerModel(simplex, integerColumns,
        std::chrono::steady_clock::now() + std::chrono::seconds(1), 64, [] {});
    REQUIRE(model.has_value());
    CHECK(model->at(x) == 1);
    CHECK_FALSE(model->contains(y));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    CHECK(simplex.value(y).a == mpq_class(1, 2));
    CHECK(simplex.value(y).b == 0);
}

TEST_CASE("integer model completion: negative rounding and exhausted allocations preserve the parent") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("x");
    const auto reason = SatLit::positive(1);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(mpq_class(-4, 3))), reason)));
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(mpq_class(-1, 3))), reason)));
    const std::vector<int> columns{x};
    IntegerCompletionStatistics stats;
    CHECK_FALSE(completeIntegerModel(simplex, columns,
        std::chrono::steady_clock::now() + std::chrono::seconds(1), 0, [] {}, &stats));
    CHECK(stats.exhausted);
    CHECK(stats.nodes == 0);
    CHECK_FALSE(completeIntegerModel(simplex, columns,
        std::chrono::steady_clock::time_point::min(), 64, [] {}, &stats));
    CHECK(stats.exhausted);
    const auto model = completeIntegerModel(simplex, columns,
        std::chrono::steady_clock::now() + std::chrono::seconds(1), 64, [] {});
    REQUIRE(model.has_value());
    CHECK(model->at(x) == -1);
    REQUIRE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(mpq_class(-4, 3))), reason)));
    REQUIRE(simplex.check() == GeneralSimplex::Result::Sat);
    CHECK(simplex.value(x).a == mpq_class(-4, 3));
    CHECK(simplex.debugCheckInvariants());
}
