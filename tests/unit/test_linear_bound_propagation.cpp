#include "search/linear/LinearBoundPropagation.h"
#include <doctest/doctest.h>
#include <algorithm>
#include <array>
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

TEST_CASE("LinearBoundPropagation: context refutations preserve strict real endpoints and budgets") {
    const std::vector<LinearBoundRow> rows{
        {{{{"x", 1}}}, Relation::Gt, 0, {SatLit::negative(1)}},
        {{{{"x", 1}}}, Relation::Leq, 0, {SatLit::positive(2)}}};
    WorkBudget budget;
    auto conflict = LinearBoundPropagation::findConflict(rows,
        [](const std::string&) { return false; }, budget);
    REQUIRE(conflict);
    CHECK(*conflict == std::vector<SatLit>{SatLit::negative(1), SatLit::positive(2)});
    WorkBudget limited(1);
    CHECK_FALSE(LinearBoundPropagation::findConflict(rows,
        [](const std::string&) { return false; }, limited));
    WorkBudget repaired;
    CHECK_FALSE(LinearBoundPropagation::findConflict({rows.front()},
        [](const std::string&) { return false; }, repaired));
}

TEST_CASE("LinearBoundPropagation: shared guards exclude only the target endpoint's occurrences") {
    Bounds bounds;
    bounds.values[{"x", true}] = {100, false, {SatLit::positive(1), SatLit::positive(2)}};
    bounds.values[{"y", true}] = {2, false, {SatLit::positive(2), SatLit::positive(2)}};
    bounds.values[{"z", true}] = {3, false, {SatLit::positive(2)}};
    const auto result = bounds.run({{{{{"x", 1}, {"y", 1}, {"z", 1}}},
        Relation::Leq, 10, {SatLit::positive(4)}}}, true);
    REQUIRE(result.conflict);
    const auto& upper = bounds.values.at({"x", false});
    CHECK(upper.value == 5);
    CHECK(upper.reasons == std::vector<SatLit>{SatLit::positive(2), SatLit::positive(4)});
}

TEST_CASE("LinearBoundPropagation: overlapping explanations close a coupled cone within the existing work budget") {
    const std::vector<int> weights{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59};
    int total = 1;
    for (int weight : weights) total += weight;
    std::vector<LinearBoundRow> rows;
    LinearFormKey sum;
    SatVar reason = 0;
    for (size_t i = 0; i < weights.size(); ++i) {
        const auto name = "x" + std::to_string(i);
        sum.terms.emplace_back(name, 1);
        rows.push_back({{{{name, 1}}}, Relation::Geq, 0, {SatLit::positive(++reason)}});
    }
    for (size_t i = 0; i < weights.size(); ++i) {
        LinearFormKey form;
        for (size_t j = 0; j < weights.size(); ++j)
            form.terms.emplace_back("x" + std::to_string(j), weights[i] - (i == j ? total : 0));
        rows.push_back({std::move(form), Relation::Leq, 0, {SatLit::positive(++reason)}});
    }
    rows.push_back({sum, Relation::Geq, 1, {SatLit::positive(++reason)}});
    rows.push_back({sum, Relation::Leq, total - 2, {SatLit::positive(++reason)}});
    WorkBudget budget(262144);
    const auto conflict = LinearBoundPropagation::findConflict(rows,
        [](const std::string&) { return true; }, budget);
    REQUIRE(conflict);
    CHECK_FALSE(conflict->empty());
    for (SatLit guard : *conflict) CHECK(guard.var > 0);
}

TEST_CASE("LinearBoundPropagation: common forms close integer cones without changing real semantics") {
    const std::vector<LinearBoundRow> rows{
        {{{{"x", -4}, {"y", 1}, {"z", 1}}}, Relation::Leq, 0, {SatLit::positive(7)}},
        {{{{"x", 1}, {"y", -4}, {"z", 1}}}, Relation::Leq, 0, {SatLit::positive(8)}},
        {{{{"x", 2}, {"y", 2}, {"z", -3}}}, Relation::Leq, 0, {SatLit::positive(9)}},
        {{{{"x", 1}, {"y", 1}, {"z", 1}}}, Relation::Geq, 1, {SatLit::positive(10)}},
        {{{{"x", 1}, {"y", 1}, {"z", 1}}}, Relation::Leq, 3, {SatLit::positive(11)}}};
    for (bool integer : {false, true}) {
        Bounds bounds;
        for (const auto& name : {"x", "y", "z"}) {
            bounds.values[{name, true}] = {0, false, {}};
            bounds.values[{name, false}] = {3, false, {}};
        }
        const auto result = bounds.run(rows, integer);
        CHECK_FALSE(result.exhausted);
        CHECK(result.conflict == integer);
        for (const auto& [key, value] : bounds.values) {
            (void)value;
            CHECK((key.first == "x" || key.first == "y" || key.first == "z"));
        }
        if (!integer) {
            CHECK(bounds.values.at({"x", true}).value == mpq_class(1, 5));
            CHECK(bounds.values.at({"z", true}).value == mpq_class(2, 5));
        }
    }
}

TEST_CASE("LinearBoundPropagation: rational common forms are not implicitly integral") {
    Bounds bounds;
    for (const auto& [name, value] : std::vector<std::pair<std::string, int>>{{"x", 0}, {"y", 1}, {"z", 0}}) {
        bounds.values[{name, true}] = {value, false, {}};
        bounds.values[{name, false}] = {value, false, {}};
    }
    const std::vector<LinearBoundRow> rows{
        {{{{"x", 1}, {"y", mpq_class(1, 2)}, {"z", mpq_class(1, 2)}}}, Relation::Geq, mpq_class(1, 2), {}},
        {{{{"x", 1}, {"y", mpq_class(1, 2)}, {"z", mpq_class(1, 2)}}}, Relation::Leq, mpq_class(1, 2), {}},
        {{{{"x", -1}, {"y", mpq_class(1, 2)}, {"z", mpq_class(1, 2)}}}, Relation::Leq, mpq_class(1, 2), {}},
        {{{{"x", 1}, {"y", mpq_class(-3, 2)}, {"z", mpq_class(1, 2)}}}, Relation::Leq, mpq_class(-3, 2), {}}};
    const auto result = bounds.run(rows, true);
    CHECK_FALSE(result.exhausted);
    CHECK_FALSE(result.conflict);
}

TEST_CASE("LinearBoundPropagation: common-form explanations preserve every independent integer witness") {
    for (int p : {1, 2}) for (int q : {1, 2}) for (int r : {1, 2}) {
        for (int cap : {2, 3, 5}) {
            CAPTURE(p); CAPTURE(q); CAPTURE(r); CAPTURE(cap);
            const std::vector<std::string> names{"__xolver_local_linear_form", "y", "z"};
            std::vector<LinearBoundRow> rows;
            for (size_t i = 0; i < 3; ++i) {
                const int weight = i == 0 ? p : i == 1 ? q : r;
                LinearBoundRow row{{}, Relation::Leq, 0, {SatLit::positive(7 + i)}};
                for (size_t j = 0; j < 3; ++j) row.lhs.terms.emplace_back(names[j], weight - (i == j ? 7 : 0));
                rows.push_back(std::move(row));
            }
            rows.push_back({{{{names[0], 1}, {names[1], 1}, {names[2], 1}}}, Relation::Geq, 1, {SatLit::positive(10)}});
            rows.push_back({{{{names[0], 1}, {names[1], 1}, {names[2], 1}}}, Relation::Leq, cap, {SatLit::positive(11)}});
            Bounds bounds;
            for (size_t i = 0; i < 3; ++i) {
                bounds.values[{names[i], true}] = {0, false, {SatLit::positive(1 + i)}};
                bounds.values[{names[i], false}] = {3, false, {SatLit::positive(4 + i)}};
            }
            const auto result = bounds.run(rows, true);
            CHECK_FALSE(result.exhausted);
            for (int x = -1; x <= 4; ++x) for (int y = -1; y <= 4; ++y) for (int z = -1; z <= 4; ++z) {
                const int sum = x + y + z;
                const std::array<bool, 12> facts{false, x >= 0, y >= 0, z >= 0, x <= 3, y <= 3, z <= 3,
                    p*sum <= 7*x, q*sum <= 7*y, r*sum <= 7*z, sum >= 1, sum <= cap};
                auto premises = [&](const std::vector<SatLit>& reasons) {
                    return std::all_of(reasons.begin(), reasons.end(), [&](SatLit literal) {
                        return literal.sign ? facts.at(literal.var) : !facts.at(literal.var);
                    });
                };
                if (result.conflictReasons) CHECK_FALSE(premises(*result.conflictReasons));
                for (const auto& [key, bound] : bounds.values) {
                    REQUIRE((key.first == names[0] || key.first == names[1] || key.first == names[2]));
                    const int value = key.first == names[0] ? x : key.first == names[1] ? y : z;
                    CHECK((!premises(bound.reasons) || (key.second ? value >= bound.value : value <= bound.value)));
                }
            }
        }
    }
}
