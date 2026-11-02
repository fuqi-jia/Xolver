#include <doctest/doctest.h>
#include "search/candidate/CandidateModelSearch.h"
#include "evidence/ArithModelValidator.h"

using namespace xolver;

namespace {
void checkSparseCandidate(bool integers, int dimensions, int target) {
    NativeTerms ir;
    const auto boolean = ir.allocateSortId();
    ir.registerSort(boolean, SortKind::Bool);
    ir.setBoolSortId(boolean);
    const auto numeric = ir.allocateSortId();
    ir.registerSort(numeric, integers ? SortKind::Int : SortKind::Real);
    if (integers) ir.setIntSortId(numeric);
    else ir.setRealSortId(numeric);
    const auto number = [&](int value) {
        if (integers) return ir.add(TermExpr{Kind::ConstInt, numeric, {}, Payload(int64_t(value))});
        return ir.add(TermExpr{Kind::ConstReal, numeric, {}, Payload(std::to_string(value))});
    };
    const auto zero = number(0), one = number(1);
    TermExpr sum;
    sum.kind = Kind::Add;
    sum.sort = numeric;
    for (int i = 0; i < dimensions; ++i) {
        const auto variable = ir.add(TermExpr{Kind::Variable, numeric, {},
                                             Payload("x" + std::to_string(i))});
        ir.addAssertion(ir.add({Kind::Geq, boolean, {variable, zero}, {}}));
        ir.addAssertion(ir.add({Kind::Leq, boolean, {variable, one}, {}}));
        sum.children.push_back(variable);
    }
    ir.addAssertion(ir.add({Kind::Eq, boolean, {ir.add(std::move(sum)), number(target)}, {}}));
    CandidateModelSearch::Config config;
    config.wallClockBudget = std::chrono::seconds(5);
    const auto result = CandidateModelSearch(ir, integers ? "QF_LIA" : "QF_LRA", config).run();
    REQUIRE(result.found);
    CHECK(result.strategy == "10a-rational");
    REQUIRE(result.model.assignments.size() == static_cast<size_t>(dimensions));
    ArithModelValidator::NumAssignment assignment;
    mpq_class total = 0;
    for (const auto& [name, value] : result.model.assignments) {
        const mpq_class q(value);
        CHECK(q >= 0);
        CHECK(q <= 1);
        if (integers) CHECK(q.get_den() == 1);
        total += q;
        assignment.emplace(name, q);
    }
    CHECK(total == target);
    ArithModelValidator::BoolAssignment booleans;
    ArithModelValidator validator(ir, assignment, booleans);
    CHECK(validator.validate(ir.assertions()) == ArithModelValidator::Verdict::Satisfied);
}
}

TEST_CASE("candidate height search reaches sparse integer points in more than thirty dimensions") {
    checkSparseCandidate(true, 64, 3);
}

TEST_CASE("candidate height search reaches sparse real points in more than thirty dimensions") {
    checkSparseCandidate(false, 32, 2);
}
