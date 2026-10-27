#include "search/linear/IntegerAffineProjection.h"
#include <doctest/doctest.h>

using namespace xolver;

namespace {
ActiveLinearAtom equality(const LinearFormKey& lhs, long rhs, SatVar reason) {
    return {NullExpr, -1, Relation::Eq, true, lhs, mpq_class(rhs), SatLit::positive(reason)};
}
}

TEST_CASE("IntegerAffineProjection: conditional equalities expose the form lattice") {
    const LinearFormKey form{{{"x", 2}, {"y", -1}, {"z", 512}}};
    std::vector<ActiveLinearAtom> atoms{
        equality(LinearFormKey{{{"a", -1}, {"y", 1}}}, 0, 1),
        equality(LinearFormKey{{{"a", -1}, {"x", 2}}}, 4096, 2)};
    WorkBudget budget(8192);
    const auto projected = projectIntegerAffineForm(form, atoms, budget);
    REQUIRE(projected.has_value());
    CHECK(projected->offset == 4096);
    CHECK(projected->step == 512);
    CHECK(projected->reasons == std::vector<SatLit>{SatLit::positive(1), SatLit::positive(2)});

    // A new context without those equalities must recover the original step.
    WorkBudget emptyBudget(8192);
    const auto unconditioned = projectIntegerAffineForm(form, {}, emptyBudget);
    REQUIRE(unconditioned.has_value());
    CHECK(unconditioned->offset == 0);
    CHECK(unconditioned->step == 1);
    CHECK(unconditioned->reasons.empty());

    // Negated equality is a disequality and cannot justify a projection.
    atoms.resize(1);
    atoms[0].value = false;
    atoms[0].lit = SatLit::negative(1);
    WorkBudget negatedBudget(8192);
    const auto negated = projectIntegerAffineForm(form, atoms, negatedBudget);
    REQUIRE(negated.has_value());
    CHECK(negated->step == 1);
    CHECK(negated->reasons.empty());
}

TEST_CASE("IntegerAffineProjection: exact witnesses remain in arbitrary signed lattices") {
    for (long step : {2L, 3L, 5L, 512L}) {
        for (long rhs : {-7L, 0L, 11L}) {
            for (long sign : {-1L, 1L}) {
                const LinearFormKey form{{{"x", 2}, {"y", -1}, {"z", mpq_class(step)}}};
                std::vector<ActiveLinearAtom> atoms{
                    equality(LinearFormKey{{{"x", 2*sign}, {"y", -sign}}}, rhs*sign, 3)};
                WorkBudget budget(8192);
                const auto projected = projectIntegerAffineForm(form, atoms, budget);
                REQUIRE(projected.has_value());
                CHECK(projected->offset == rhs);
                CHECK(projected->step == step);
                CHECK(projected->reasons == std::vector<SatLit>{SatLit::positive(3)});
                for (long x = -3; x <= 3; ++x) {
                    for (long z = -3; z <= 3; ++z) {
                        const mpz_class y = 2*x-rhs;
                        const mpz_class value = 2*x-y+step*z;
                        const mpz_class delta = value-projected->offset;
                        CHECK(delta % projected->step == 0);
                    }
                }
            }
        }
    }
}

TEST_CASE("IntegerAffineProjection: constant forms and resource exhaustion retain their meaning") {
    const LinearFormKey form{{{"x", 2}, {"y", -1}}};
    std::vector<ActiveLinearAtom> atoms{equality(form, 7, 4)};
    WorkBudget budget(8192);
    const auto fixed = projectIntegerAffineForm(form, atoms, budget);
    REQUIRE(fixed.has_value());
    CHECK(fixed->offset == 7);
    CHECK(fixed->step == 0);
    CHECK(fixed->reasons == std::vector<SatLit>{SatLit::positive(4)});
    WorkBudget exhausted(1);
    CHECK_FALSE(projectIntegerAffineForm(form, atoms, exhausted).has_value());
    WorkBudget fractionalBudget(8192);
    CHECK_FALSE(projectIntegerAffineForm(LinearFormKey{{{"x", mpq_class(1, 2)}}}, atoms,
                                        fractionalBudget).has_value());
}

TEST_CASE("IntegerAffineProjection: unchanged lattices retain unconditional explanations") {
    const LinearFormKey form{{{"x", 1}, {"y", 1}, {"z", 1}}};
    std::vector<ActiveLinearAtom> atoms{
        equality(LinearFormKey{{{"x", 1}, {"y", -1}}}, 7, 5)};
    WorkBudget budget(8192);
    const auto projected = projectIntegerAffineForm(form, atoms, budget);
    REQUIRE(projected.has_value());
    CHECK(projected->offset == 0);
    CHECK(projected->step == 1);
    CHECK(projected->reasons.empty());
}

TEST_CASE("IntegerAffineContext: repeated projections ignore unrelated equality components") {
    std::vector<ActiveLinearAtom> atoms{
        equality(LinearFormKey{{{"x", 2}, {"y", -1}}}, 7, 1)};
    for (int i = 0; i < 1000; ++i)
        atoms.push_back(equality(LinearFormKey{{{"a" + std::to_string(i), 1},
                                               {"b" + std::to_string(i), -1}}}, i, i + 10));
    WorkBudget preparation(8192);
    const auto context = IntegerAffineContext::build(atoms, preparation);
    REQUIRE(context.has_value());
    for (long step : {2L, 3L, 512L}) {
        const LinearFormKey form{{{"x", 2}, {"y", -1}, {"z", mpq_class(step)}}};
        WorkBudget projection(128);
        const auto result = context->project(form, projection);
        REQUIRE(result.has_value());
        CHECK(result->offset == 7);
        CHECK(result->step == step);
        CHECK(result->reasons == std::vector<SatLit>{SatLit::positive(1)});
        CHECK(projection.used() < 128);
    }
    // The compatibility API charges preparation too; it cannot scan a
    // thousand source equations within the small per-projection budget.
    WorkBudget oneShot(128);
    CHECK_FALSE(projectIntegerAffineForm(LinearFormKey{{{"x", 2}, {"y", -1}, {"z", 512}}},
                                         atoms, oneShot).has_value());
}

TEST_CASE("IntegerAffineContext: indirect dependencies and fresh source snapshots retain explanations") {
    std::vector<ActiveLinearAtom> atoms{
        equality(LinearFormKey{{{"a", -1}, {"z", 1}}}, 3, 2),
        equality(LinearFormKey{{{"a", 1}, {"y", -4}}}, 5, 3)};
    const LinearFormKey form{{{"x", 2}, {"z", 1}}};
    WorkBudget preparation(8192);
    const auto context = IntegerAffineContext::build(atoms, preparation);
    REQUIRE(context.has_value());
    WorkBudget projection(8192);
    const auto result = context->project(form, projection);
    REQUIRE(result.has_value());
    CHECK(result->offset == 8);
    CHECK(result->step == 2);
    CHECK(result->reasons == std::vector<SatLit>{SatLit::positive(2), SatLit::positive(3)});
    // A backtracked source is a negated equality and cannot support the new
    // context. Reusing prepared rows within a check never retains this premise
    // into another check.
    atoms[1].value = false;
    atoms[1].lit = SatLit::negative(3);
    WorkBudget nextPreparation(8192), nextProjection(8192);
    const auto next = IntegerAffineContext::build(atoms, nextPreparation);
    REQUIRE(next.has_value());
    const auto unconditioned = next->project(form, nextProjection);
    REQUIRE(unconditioned.has_value());
    CHECK(unconditioned->step == 1);
    CHECK(unconditioned->offset == 0);
    CHECK(unconditioned->reasons.empty());
}
