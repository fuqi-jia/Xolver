#include "search/linear/LinearBoundPropagation.h"
#include <doctest/doctest.h>
#include <map>

using namespace xolver;

namespace {
struct Bounds {
    std::map<std::pair<std::string, bool>, ExplainedLinearBound> values;

    LinearBoundPropagationResult run(const std::vector<LinearBoundRow>& rows,
                                    bool integer, size_t limit = 8192) {
        WorkBudget budget(limit);
        return LinearBoundPropagation::run(rows,
            [&](const std::string& variable, bool lower) -> std::optional<ExplainedLinearBound> {
                const auto found = values.find({variable, lower});
                return found == values.end() ? std::nullopt : std::optional(found->second);
            },
            [&](const std::string& variable, bool lower, const ExplainedLinearBound& bound) {
                const auto key = std::make_pair(variable, lower);
                const auto found = values.find(key);
                if (found != values.end()) {
                    const auto& old = found->second;
                    if ((lower ? old.value > bound.value : old.value < bound.value) ||
                            (old.value == bound.value && (old.strict || !bound.strict)))
                        return LinearBoundUpdate::Unchanged;
                }
                values[key] = bound;
                const auto opposite = values.find({variable, !lower});
                if (opposite != values.end()) {
                    const auto& lo = values.at({variable, true});
                    const auto& hi = values.at({variable, false});
                    if (lo.value > hi.value || (lo.value == hi.value && (lo.strict || hi.strict)))
                        return LinearBoundUpdate::Conflict;
                }
                return LinearBoundUpdate::Changed;
            }, [&](const std::string&) { return integer; }, budget);
    }
};
}

TEST_CASE("LinearBoundPropagation: strict rational bounds respect the target sort") {
    for (bool integer : {false, true}) {
        Bounds bounds;
        bounds.values[{"y", false}] = {mpq_class(1, 2), true, {SatLit::positive(1)}};
        const auto result = bounds.run({{{{{"x", 1}, {"y", -1}}}, Relation::Leq,
                                        mpq_class(1, 3), {SatLit::negative(2)}}}, integer);
        CHECK_FALSE(result.conflict);
        const auto& upper = bounds.values.at({"x", false});
        CHECK(upper.value == (integer ? mpq_class(0) : mpq_class(5, 6)));
        CHECK(upper.strict == !integer);
        CHECK(upper.reasons == std::vector<SatLit>{SatLit::positive(1), SatLit::negative(2)});
    }
    Bounds negative;
    negative.values[{"y", true}] = {mpq_class(-1, 2), false, {SatLit::positive(1)}};
    negative.run({{{{{"x", -2}, {"y", 1}}}, Relation::Gt, 0, {SatLit::positive(2)}}}, true);
    CHECK(negative.values.at({"y", true}).value == mpq_class(-1, 2));
    // A lower bound on y does not imply an upper bound on x here.
    CHECK(negative.values.count({"x", false}) == 0);
}

TEST_CASE("LinearBoundPropagation: repeated variables merge before integer rounding") {
    for (bool integer : {false, true}) {
        Bounds bounds;
        bounds.values[{"y", true}] = {2, false, {SatLit::positive(1)}};
        bounds.values[{"y", false}] = {2, false, {SatLit::positive(2)}};
        const auto result = bounds.run({{{{{"x", 1}, {"y", -1}, {"x", 1}}},
                                         Relation::Eq, 1, {SatLit::positive(3)}}}, integer);
        CHECK(result.conflict == integer);
        if (!integer) {
            CHECK(bounds.values.at({"x", true}).value == mpq_class(3, 2));
            CHECK(bounds.values.at({"x", false}).value == mpq_class(3, 2));
        }
    }
}

TEST_CASE("LinearBoundPropagation: signed rows and their explanations preserve independent witnesses") {
    for (int a : {-3, -1, 1, 2}) for (int b : {-3, -1, 1, 2}) {
        for (int rhs : {-2, 0, 3}) for (auto rel : {Relation::Leq, Relation::Geq, Relation::Eq}) {
            CAPTURE(a); CAPTURE(b); CAPTURE(rhs); CAPTURE(int(rel));
            Bounds bounds;
            bounds.values[{"y", true}] = {-2, false, {SatLit::positive(1)}};
            bounds.values[{"y", false}] = {2, false, {SatLit::positive(2)}};
            const auto result = bounds.run({{{{{"x", a}, {"y", b}}}, rel, rhs,
                                             {SatLit::negative(3)}}}, true);
            CHECK_FALSE(result.exhausted);
            for (const auto& [key, bound] : bounds.values) {
                for (int x = -5; x <= 5; ++x) for (int y = -5; y <= 5; ++y) {
                    const int lhs = a*x+b*y;
                    const bool holds = rel == Relation::Eq ? lhs == rhs
                        : rel == Relation::Leq ? lhs <= rhs : lhs >= rhs;
                    bool premises = true;
                    for (const auto literal : bound.reasons) {
                        const bool truth = literal.var == 1 ? y >= -2
                            : literal.var == 2 ? y <= 2 : !holds;
                        premises &= literal.sign ? truth : !truth;
                    }
                    const mpq_class value(key.first == "x" ? x : y);
                    const bool satisfies = key.second ? value >= bound.value : value <= bound.value;
                    CHECK((!premises || satisfies));
                }
            }
        }
    }
}

TEST_CASE("LinearBoundPropagation: exhausted or invalid inputs yield no unsupported fact") {
    const LinearBoundRow row{{{{"x", 1}, {"y", -1}}}, Relation::Eq, 1, {SatLit::positive(2)}};
    Bounds limited;
    limited.values[{"y", true}] = {0, false, {SatLit::positive(1)}};
    CHECK(limited.run({row}, true, 1).exhausted);
    CHECK(limited.values.size() == 1);
    Bounds unexplained;
    unexplained.values[{"y", true}] = {0, false, {SatLit::positive(0)}};
    CHECK(unexplained.run({row}, true).updates == 0);
    CHECK(unexplained.values.size() == 1);
}

TEST_CASE("LinearBoundPropagation: unconditional facts need no conditional guard") {
    Bounds bounds;
    bounds.values[{"y", true}] = {0, false, {}};
    const LinearBoundRow row{{{{"x", 1}, {"y", -1}}}, Relation::Eq, 1, {}};
    CHECK(bounds.run({row}, true).updates == 1);
    const auto& lower = bounds.values.at({"x", true});
    CHECK(lower.value == 1);
    CHECK(lower.reasons.empty());
}
