#include <doctest/doctest.h>
#include "search/linear/IntegerAffineModel.h"

using namespace xolver;

namespace {
NormalizedConstraint constraint(int a, int b, Relation relation, int rhs) {
    LinearFormKey form;
    if (a) form.terms.push_back({"x", mpq_class(a)});
    if (b) form.terms.push_back({"y", mpq_class(b)});
    return {form, mpq_class(rhs), relation};
}
}

TEST_CASE("integer affine model: exact bounded solutions agree with exhaustive integer assignments") {
    for (int a = -3; a <= 3; ++a) for (int b = -3; b <= 3; ++b) {
        if (!a || !b) continue;
        for (int rhs = -6; rhs <= 6; ++rhs) {
            CAPTURE(a); CAPTURE(b); CAPTURE(rhs);
            std::vector<NormalizedConstraint> constraints{
                constraint(a, b, Relation::Eq, rhs),
                constraint(1, 0, Relation::Leq, 3), constraint(-1, 0, Relation::Leq, 3),
                constraint(0, 1, Relation::Leq, 3), constraint(0, -1, Relation::Leq, 3),
                constraint(1, 0, Relation::Neq, 0)};
            bool exists = false;
            for (int x = -3; x <= 3; ++x) for (int y = -3; y <= 3; ++y)
                exists |= a*x + b*y == rhs && x != 0;
            const auto model = findIntegerAffineModel(constraints, {{"x", 0}, {"y", 0}});
            CHECK(model.has_value() == exists);
            if (model) {
                const auto x = model->at("x"), y = model->at("y");
                CHECK(x.get_den() == 1); CHECK(y.get_den() == 1);
                CHECK(a*x + b*y == rhs);
                CHECK(x >= -3); CHECK(x <= 3); CHECK(y >= -3); CHECK(y <= 3);
                CHECK(x != 0);
            }
        }
    }
}

TEST_CASE("integer affine model: large coprime coefficients, one-sided bounds and exclusions") {
    const mpz_class a("4294967296"), b("3123612579");
    const NormalizedConstraint equation{LinearFormKey{{{"x", mpq_class(a)}, {"y", mpq_class(b)}}}, 24, Relation::Eq};
    auto constraints = std::vector<NormalizedConstraint>{equation, constraint(0, 1, Relation::Leq, -1)};
    const auto model = findIntegerAffineModel(constraints, {{"x", 0}, {"y", -1}});
    REQUIRE(model);
    CHECK(a*model->at("x") + b*model->at("y") == 24);
    CHECK(model->at("y") <= -1);
    constraints.push_back({LinearFormKey{{{"y", 1}}}, model->at("y"), Relation::Neq});
    const auto different = findIntegerAffineModel(constraints, {{"x", 0}, {"y", -1}});
    REQUIRE(different);
    CHECK(different->at("y") != model->at("y"));
    CHECK(a*different->at("x") + b*different->at("y") == 24);
    CHECK(different->at("y") <= -1);
}

TEST_CASE("integer affine model: coupled equations, seed coordinates and inconsistent systems") {
    std::vector<NormalizedConstraint> constraints{
        constraint(2, 3, Relation::Eq, 7), constraint(1, -1, Relation::Eq, 1),
        {LinearFormKey{{{"z", 1}}}, 3, Relation::Leq}};
    const auto unique = findIntegerAffineModel(constraints, {{"z", 2}});
    REQUIRE(unique);
    CHECK(unique->at("x") == 2); CHECK(unique->at("y") == 1); CHECK(unique->at("z") == 2);
    CHECK_FALSE(findIntegerAffineModel(constraints, {{"z", 4}}));
    CHECK_FALSE(findIntegerAffineModel(constraints, {}));
    constraints.push_back(constraint(1, -1, Relation::Eq, 2));
    CHECK_FALSE(findIntegerAffineModel(constraints, {{"z", 2}}));
    CHECK_FALSE(findIntegerAffineModel({constraint(2, 4, Relation::Eq, 1)}, {{"x", 0}, {"y", 0}}));
}
