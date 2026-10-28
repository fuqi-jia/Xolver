#include "search/linear/LinearBoundPropagation.h"
#include "search/nia/core/LinearNiaDomainReasoner.h"
#include <doctest/doctest.h>
#include <algorithm>
#include <map>

using namespace xolver;

namespace {
// Check the returned certificate directly against the original rows, without
// using the aggregator's normalization or row selection.
void checkCertificate(const std::vector<LinearBoundRow>& rows,
                      const LinearAggregateConflict& conflict) {
    std::map<std::string, mpq_class> coefficients;
    mpq_class rhs = 0;
    bool strict = false;
    std::vector<SatLit> reasons;
    REQUIRE_FALSE(conflict.multipliers.empty());
    for (const auto& [index, multiplier] : conflict.multipliers) {
        REQUIRE(index < rows.size());
        REQUIRE(multiplier > 0);
        const auto& row = rows[index];
        REQUIRE((row.rel == Relation::Leq || row.rel == Relation::Lt ||
                 row.rel == Relation::Geq || row.rel == Relation::Gt));
        const int sign = row.rel == Relation::Geq || row.rel == Relation::Gt ? -1 : 1;
        for (const auto& [variable, coefficient] : row.lhs.terms)
            coefficients[variable] += sign * multiplier * coefficient;
        rhs += sign * multiplier * row.rhs;
        strict |= row.rel == Relation::Lt || row.rel == Relation::Gt;
        reasons.insert(reasons.end(), row.reasons.begin(), row.reasons.end());
    }
    for (const auto& [variable, coefficient] : coefficients) {
        CAPTURE(variable);
        CHECK(coefficient == 0);
    }
    CHECK((rhs < 0 || (rhs == 0 && strict)));
    CHECK(rhs == conflict.rhs);
    CHECK(strict == conflict.strict);
    for (const auto reason : reasons)
        CHECK(std::find(conflict.reasons.begin(), conflict.reasons.end(), reason) != conflict.reasons.end());
    for (const auto reason : conflict.reasons)
        CHECK(std::find(reasons.begin(), reasons.end(), reason) != reasons.end());
}
}

TEST_CASE("Linear aggregation: scaled capacity inequalities have a checkable conflict") {
    for (int resources : {2, 3, 5}) {
        for (int items : {resources - 1, resources + 1}) {
            std::vector<LinearBoundRow> rows;
            for (int item = 0; item < items; ++item) {
                const mpq_class scale(item + 2, item + 3);
                LinearBoundRow row{{}, Relation::Geq, scale, {SatLit::positive(item + 1)}};
                for (int resource = 0; resource < resources; ++resource)
                    row.lhs.terms.emplace_back(std::to_string(item) + ":" + std::to_string(resource), scale);
                rows.push_back(std::move(row));
            }
            for (int resource = 0; resource < resources; ++resource) {
                const mpq_class scale(resource + 3, resource + 2);
                LinearBoundRow row{{}, Relation::Leq, scale, {SatLit::negative(items + resource + 1)}};
                for (int item = 0; item < items; ++item)
                    row.lhs.terms.emplace_back(std::to_string(item) + ":" + std::to_string(resource), scale);
                rows.push_back(std::move(row));
            }
            WorkBudget budget(8192);
            const auto conflict = LinearBoundPropagation::aggregateConflict(rows, budget);
            CHECK(bool(conflict) == (items > resources));
            if (conflict) checkCertificate(rows, *conflict);
        }
    }
}

TEST_CASE("Linear aggregation: strict rational cycles and duplicate coefficients") {
    std::vector<LinearBoundRow> rows{
        {{{{"x", 2}, {"y", -2}, {"x", -1}}}, Relation::Lt, mpq_class(1, 3), {SatLit::positive(1)}},
        {{{{"y", 2}, {"z", -1}}}, Relation::Leq, mpq_class(1, 6), {SatLit::negative(2)}},
        {{{{"z", 1}, {"x", -1}}}, Relation::Leq, mpq_class(-1, 2), {SatLit::positive(3)}}};
    WorkBudget budget(8192);
    const auto conflict = LinearBoundPropagation::aggregateConflict(rows, budget);
    REQUIRE(conflict);
    checkCertificate(rows, *conflict);
    CHECK(conflict->rhs == 0);
    CHECK(conflict->strict);
    rows[0].rel = Relation::Leq;
    WorkBudget feasibleBudget(8192);
    CHECK_FALSE(LinearBoundPropagation::aggregateConflict(rows, feasibleBudget));
}

TEST_CASE("Linear aggregation: missing provenance and exhausted work cannot refute") {
    std::vector<LinearBoundRow> rows{
        {{{{"x", 1}, {"y", 1}}}, Relation::Leq, 0, {SatLit::positive(1)}},
        {{{{"y", -1}, {"x", -1}}}, Relation::Leq, -1, {SatLit::positive(0)}}};
    WorkBudget budget(8192);
    CHECK_FALSE(LinearBoundPropagation::aggregateConflict(rows, budget));
    rows[1].reasons = {SatLit::negative(2)};
    WorkBudget exhausted(1);
    CHECK_FALSE(LinearBoundPropagation::aggregateConflict(rows, exhausted));
    WorkBudget complete(8192);
    const auto conflict = LinearBoundPropagation::aggregateConflict(rows, complete);
    REQUIRE(conflict);
    checkCertificate(rows, *conflict);
}

TEST_CASE("Linear aggregation: constant rows and unconditional premises") {
    for (auto relation : {Relation::Leq, Relation::Lt, Relation::Geq, Relation::Gt}) {
        const bool strict = relation == Relation::Lt || relation == Relation::Gt;
        const int direction = relation == Relation::Geq || relation == Relation::Gt ? -1 : 1;
        for (int rhs : {-1, 0, 1}) {
            const std::vector<LinearBoundRow> rows{
                {{{{"x", 1}, {"x", -1}}}, relation, rhs, {}}};
            WorkBudget budget(8192);
            const auto conflict = LinearBoundPropagation::aggregateConflict(rows, budget);
            CHECK(bool(conflict) == (direction * rhs < 0 || (rhs == 0 && strict)));
            if (conflict) checkCertificate(rows, *conflict);
        }
    }
}

TEST_CASE("Linear aggregation: feasible rational witnesses never become conflicts") {
    for (int seed = 0; seed < 40; ++seed) {
        std::vector<LinearBoundRow> rows;
        for (int index = 0; index < 17; ++index) {
            const mpq_class x(seed - 7, 3), y(11 - seed, 5), z(seed + 3, 7);
            const mpq_class a((index + seed) % 7 - 3, 3), b((2 * index + seed) % 9 - 4, 5);
            const mpq_class c((3 * index + seed) % 11 - 5, 7);
            const mpq_class slack((index + seed) % 3, 11);
            const auto rel = index % 2 ? Relation::Leq : Relation::Geq;
            rows.push_back({{{{"x", a}, {"y", b}, {"z", c}}}, rel,
                a * x + b * y + c * z + (index % 2 ? slack : -slack), {}});
        }
        WorkBudget budget(8192);
        CHECK_FALSE(LinearBoundPropagation::aggregateConflict(rows, budget));
    }
}

TEST_CASE("LinearNiaDomain: aggregate conflicts retain every conditional premise") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const std::vector<NormalizedNiaConstraint> constraints{
        {kernel->sub(x, y), Relation::Leq, SatLit::positive(1)},
        {kernel->sub(y, z), Relation::Leq, SatLit::negative(2)},
        {kernel->sub(kernel->sub(x, z), kernel->mkConst(1)), Relation::Geq, SatLit::positive(3)}};
    LinearNiaDomainReasoner reasoner(*kernel);
    DomainStore domains;
    const auto result = reasoner.run(constraints, domains);
    REQUIRE(result.kind == NiaReasoningKind::Conflict);
    REQUIRE(result.conflict);
    for (const auto literal : {SatLit::positive(1), SatLit::negative(2), SatLit::positive(3)})
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), literal) != result.conflict->clause.end());
    for (size_t omitted = 0; omitted < constraints.size(); ++omitted) {
        auto subset = constraints;
        subset.erase(subset.begin() + omitted);
        DomainStore independent;
        CHECK(reasoner.run(subset, independent).kind != NiaReasoningKind::Conflict);
    }
}
