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

TEST_CASE("integer affine repair: free coordinates move to boundaries while dependents follow") {
    for (int sign : {-1, 1}) {
        std::vector<NormalizedConstraint> constraints{
            {LinearFormKey{{{"x",1},{"y",-2},{"z",3}}},0,Relation::Eq},
            {LinearFormKey{{{"x",-sign}}},-1,Relation::Leq},
            {LinearFormKey{{{"z",-1}}},0,Relation::Leq}};
        IntegerPoint relaxation{{"x",sign},{"y",mpq_class(sign,2)},{"z",0}};
        // Two free coordinates exceed the complete point/line constructor.
        CHECK_FALSE(findIntegerAffineModel(constraints,{{"x",sign},{"y",sign},{"z",0}}));
        WorkBudget budget(8192);
        const auto model=repairIntegerAffineModel(constraints,relaxation,budget);
        REQUIRE(model);
        CHECK(model->at("x")-2*model->at("y")+3*model->at("z")==0);
        CHECK(sign*model->at("x")>=1);
        CHECK(model->at("z")>=0);
        for (const auto& [name,value] : *model) {
            CAPTURE(name);
            CHECK(value.get_den()==1);
        }
    }
}

TEST_CASE("integer affine repair: offsets and forbidden boundaries retain their meaning") {
    std::vector<NormalizedConstraint> constraints{
        {LinearFormKey{{{"t",1}}},1,Relation::Eq},
        {LinearFormKey{{{"t",-7},{"x",1},{"y",-2},{"z",3}}},0,Relation::Eq},
        {LinearFormKey{{{"x",-1}}},-8,Relation::Leq},
        {LinearFormKey{{{"x",1}}},8,Relation::Neq},
        {LinearFormKey{{{"z",-1}}},0,Relation::Leq}};
    WorkBudget budget(8192);
    const auto model=repairIntegerAffineModel(constraints,{{"t",1},{"x",8},{"y",mpq_class(1,2)},{"z",0}},budget);
    REQUIRE(model);
    CHECK(model->at("t")==1);
    CHECK(model->at("x")-2*model->at("y")+3*model->at("z")==7);
    CHECK(model->at("x")>8);
    CHECK(model->at("z")>=0);

    WorkBudget holeBudget(8192);
    const auto hole=repairIntegerAffineModel({constraint(1,-1,Relation::Eq,0),constraint(1,0,Relation::Neq,0)},{{"x",0},{"y",0}},holeBudget);
    REQUIRE(hole);
    CHECK(hole->at("x")==hole->at("y"));
    CHECK(hole->at("x")!=0);
}

TEST_CASE("integer affine repair: exhaustion and unsupported or infeasible sources propose no witness") {
    const std::vector<NormalizedConstraint> impossible{constraint(2,0,Relation::Eq,1)};
    WorkBudget budget(8192);
    CHECK_FALSE(repairIntegerAffineModel(impossible,{{"x",mpq_class(1,2)}},budget));
    WorkBudget tiny(1);
    CHECK_FALSE(repairIntegerAffineModel({constraint(1,-1,Relation::Eq,0)},{{"x",mpq_class(1,2)},{"y",mpq_class(1,2)}},tiny));
    WorkBudget missing(8192);
    CHECK_FALSE(repairIntegerAffineModel({constraint(1,-1,Relation::Eq,0)},{{"x",0}},missing));
    WorkBudget strict(8192);
    CHECK_FALSE(repairIntegerAffineModel({constraint(1,0,Relation::Gt,0)},{{"x",0}},strict));
}

TEST_CASE("integer affine repair: every returned signed bounded witness satisfies the full source") {
    for (int a=-3;a<=3;++a) for (int b=-3;b<=3;++b) {
        std::vector<NormalizedConstraint> constraints{
            {LinearFormKey{{{"x",1},{"y",a},{"z",b}}},1,Relation::Eq},
            constraint(1,0,Relation::Leq,3),constraint(-1,0,Relation::Leq,3),
            constraint(0,1,Relation::Leq,3),constraint(0,-1,Relation::Leq,3),
            {LinearFormKey{{{"z",1}}},3,Relation::Leq},
            {LinearFormKey{{{"z",-1}}},3,Relation::Leq},
            constraint(1,0,Relation::Neq,0)};
        WorkBudget budget(8192);
        const auto model=repairIntegerAffineModel(constraints,{{"x",1-mpq_class(a+b,2)},{"y",mpq_class(1,2)},{"z",mpq_class(1,2)}},budget);
        if (!model) continue;
        CHECK(model->at("x")+a*model->at("y")+b*model->at("z")==1);
        CHECK(model->at("x")!=0);
        for (const auto& [name,value] : *model) {
            CAPTURE(name);CHECK(value.get_den()==1);CHECK(value>=-3);CHECK(value<=3);
        }
    }
}
