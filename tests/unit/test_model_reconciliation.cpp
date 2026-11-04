#include <doctest/doctest.h>
#include "search/coordination/TheoryManager.h"
#include "evidence/ArithModelValidator.h"
#include <memory>

using namespace xolver;

namespace {
struct ModelTheory : TheorySolver {
    TheoryId theory;
    TheoryModel model;
    mutable int reads = 0;
    explicit ModelTheory(TheoryId id) : theory(id) {}
    TheoryId id() const override { return theory; }
    void push() override {}
    void pop(uint32_t) override {}
    void reset() override {}
    void backtrackToLevel(int) override {}
    void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
    TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override {
        return TheoryCheckResult::consistent();
    }
    std::optional<TheoryModel> getModel() const override {
        ++reads;
        return model;
    }
};
} // namespace

TEST_CASE("Model reconciliation: source class tokens survive numeric precedence") {
    for (const bool real : {false, true}) {
        for (const bool eufFirst : {false, true}) {
            CAPTURE(real);
            CAPTURE(eufFirst);
            const std::string domain = real ? "Real" : "Int";
            const mpq_class xValue = real ? mpq_class(7, 3) : mpq_class(7);
            const mpq_class yValue = real ? mpq_class(11, 5) : mpq_class(11);
            auto primary = std::make_unique<ModelTheory>(real ? TheoryId::LRA : TheoryId::NIA);
            primary->model.assignments = {{"x", xValue.get_str()}, {"y", yValue.get_str()}};
            primary->model.numericAssignments = {{"x", RealValue::fromMpq(xValue)},
                                                 {"y", RealValue::fromMpq(yValue)}};
            auto secondary = std::make_unique<ModelTheory>(real ? TheoryId::NRA : TheoryId::LIA);
            secondary->model.assignments = {{"x", "19"}, {"y", "23"}};
            secondary->model.numericAssignments = {{"x", RealValue::fromInt(19)},
                                                   {"y", RealValue::fromInt(23)}};
            auto euf = std::make_unique<ModelTheory>(TheoryId::EUF);
            euf->model.assignments = {{"x", "@e4"}, {"y", "@e9"}};
            euf->model.functionInterps["f"] = {{domain}, domain,
                {{{"@e4"}, "@e9"}}, "#n:0"};
            TheoryModel::ArrayInterp array{domain, domain, "#n:0", {{"@e4", "@e9"}}};
            euf->model.arrayInterps["a"] = array;
            euf->model.arrayValues["array-value"] = array;
            const auto* primaryView = primary.get();
            const auto* secondaryView = secondary.get();
            const auto* eufView = euf.get();
            TheoryManager manager;
            if (eufFirst) manager.registerSolver(std::move(euf));
            manager.registerSolver(std::move(primary));
            manager.registerSolver(std::move(secondary));
            if (!eufFirst) manager.registerSolver(std::move(euf));
            const auto model = manager.getModel();
            REQUIRE(model);
            CHECK(primaryView->reads == 1);
            CHECK(secondaryView->reads == 1);
            CHECK(eufView->reads == 1);
            CHECK(model->numericAssignments.at("x").tryAsRational() == xValue);
            CHECK(model->numericAssignments.at("y").tryAsRational() == yValue);
            const auto& function = model->functionInterps.at("f");
            REQUIRE(function.entries.size() == 1);
            CHECK(function.entries[0].args == std::vector<std::string>{xValue.get_str()});
            CHECK(function.entries[0].value == yValue.get_str());
            CHECK(function.deflt == "0");
            for (const auto* value : {&model->arrayInterps.at("a"), &model->arrayValues.at("array-value")}) {
                REQUIRE(value->entries.size() == 1);
                CHECK(value->entries[0].first == "#n:" + xValue.get_str());
                CHECK(value->entries[0].second == "#n:" + yValue.get_str());
            }

            NativeTerms ir;
            ir.registerSort(0, real ? SortKind::Real : SortKind::Int);
            ir.registerSort(1, SortKind::Bool);
            ir.registerArraySort(2, 0, 0);
            const auto x = ir.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
            const auto y = ir.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
            const auto a = ir.add({Kind::Variable, 2, {}, Payload(std::string("a"))});
            const auto application = ir.add({Kind::UFApply, 0, {x}, Payload(std::string("f"))});
            const auto read = ir.add({Kind::Select, 0, {a, x}, Payload{}});
            const auto functionEquality = ir.add({Kind::Eq, 1, {application, y}, Payload{}});
            const auto arrayEquality = ir.add({Kind::Eq, 1, {read, y}, Payload{}});
            ArithModelValidator::NumAssignment numbers{{"x", xValue}, {"y", yValue}};
            ArithModelValidator::BoolAssignment booleans;
            ArithModelValidator validator(ir, numbers, booleans, model->arrayInterps, model->assignments);
            validator.setFunctionInterps(&model->functionInterps, &model->arrayValues);
            validator.setRealAssignments(&model->numericAssignments);
            CHECK(validator.validate({functionEquality, arrayEquality}) == ArithModelValidator::Verdict::Satisfied);
        }
    }
}

TEST_CASE("Model reconciliation: conflicting class values remain unconfirmed") {
    auto arithmetic = std::make_unique<ModelTheory>(TheoryId::LIA);
    arithmetic->model.assignments = {{"x", "0"}, {"y", "1"}};
    arithmetic->model.numericAssignments = {{"x", RealValue::fromInt(0)}, {"y", RealValue::fromInt(1)}};
    auto euf = std::make_unique<ModelTheory>(TheoryId::EUF);
    euf->model.assignments = {{"x", "@e4"}, {"y", "@e4"}};
    euf->model.functionInterps["f"] = {{"Int"}, "Int", {{{"@e4"}, "@e4"}}, "0"};
    TheoryManager manager;
    manager.registerSolver(std::move(arithmetic));
    manager.registerSolver(std::move(euf));
    const auto model = manager.getModel();
    REQUIRE(model);
    CHECK(model->assignments.at("x") == "0");
    CHECK(model->assignments.at("y") == "1");
    const auto& function = model->functionInterps.at("f");
    REQUIRE(function.entries.size() == 1);
    CHECK(function.entries.front().args == std::vector<std::string>{"@e4"});
    CHECK(function.entries.front().value == "@e4");
    NativeTerms ir;
    ir.registerSort(0, SortKind::Int);
    ir.registerSort(1, SortKind::Bool);
    const auto x = ir.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    const auto y = ir.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
    const auto f = ir.add({Kind::UFApply, 0, {x}, Payload(std::string("f"))});
    const auto equality = ir.add({Kind::Eq, 1, {f, y}, Payload{}});
    ArithModelValidator validator(ir, {{"x", 0}, {"y", 1}}, {});
    validator.setFunctionInterps(&model->functionInterps);
    CHECK(validator.validate({equality}) == ArithModelValidator::Verdict::Indeterminate);
}

TEST_CASE("Model reconciliation: completed numeric classes reach function tables") {
    for (const bool real : {false, true}) {
        CAPTURE(real);
        const std::string domain = real ? "Real" : "Int";
        NativeTerms ir;
        ir.registerSort(0, real ? SortKind::Real : SortKind::Int);
        ir.registerSort(1, SortKind::Bool);
        SharedTermRegistry shared;
        shared.setNativeTerms(&ir);
        auto variable = [&](const std::string& name) {
            const auto id = ir.add({Kind::Variable, 0, {}, Payload(name)});
            shared.getOrCreate(id, 0, name, false);
            return id;
        };
        const auto x = variable("x");
        const auto alias = variable("alias");
        const auto y = variable("y");
        auto euf = std::make_unique<ModelTheory>(TheoryId::EUF);
        euf->model.assignments = {{"x", "@e4"}, {"alias", "@e4"}, {"y", "@e9"}};
        euf->model.functionInterps["f"] = {{domain}, domain,
            {{{"@e4"}, "@e9"}, {{"#n:7"}, "#n:11"}}, "#n:0"};
        TheoryManager manager;
        manager.setSharedTermRegistry(&shared);
        manager.registerSolver(std::move(euf));
        const auto model = manager.getModel();
        REQUIRE(model);
        const auto xValue = model->numericAssignments.at("x").tryAsRational();
        const auto aliasValue = model->numericAssignments.at("alias").tryAsRational();
        const auto yValue = model->numericAssignments.at("y").tryAsRational();
        REQUIRE(xValue);
        REQUIRE(aliasValue);
        REQUIRE(yValue);
        CHECK(*xValue == *aliasValue);
        CHECK(*xValue != *yValue);
        CHECK(*xValue != 0);
        CHECK(*xValue != 7);
        CHECK(*xValue != 11);
        const auto& function = model->functionInterps.at("f");
        REQUIRE(function.entries.size() == 2);
        CHECK(function.entries[0].args == std::vector<std::string>{xValue->get_str()});
        CHECK(function.entries[0].value == yValue->get_str());
        CHECK(function.entries[1].args == std::vector<std::string>{"7"});
        CHECK(function.entries[1].value == "11");
        CHECK(function.deflt == "0");
        const auto application = ir.add({Kind::UFApply, 0, {x}, Payload(std::string("f"))});
        const auto aliasApplication = ir.add({Kind::UFApply, 0, {alias}, Payload(std::string("f"))});
        const auto equality = ir.add({Kind::Eq, 1, {application, y}, Payload{}});
        const auto aliasEquality = ir.add({Kind::Eq, 1, {aliasApplication, y}, Payload{}});
        ArithModelValidator::NumAssignment numbers{{"x", *xValue}, {"alias", *aliasValue}, {"y", *yValue}};
        ArithModelValidator::BoolAssignment booleans;
        ArithModelValidator validator(ir, numbers, booleans, model->arrayInterps, model->assignments);
        validator.setFunctionInterps(&model->functionInterps, &model->arrayValues);
        validator.setRealAssignments(&model->numericAssignments);
        CHECK(validator.validate({equality, aliasEquality}) == ArithModelValidator::Verdict::Satisfied);
    }
}
