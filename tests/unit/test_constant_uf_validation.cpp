#include <doctest/doctest.h>
#include "evidence/ArithModelValidator.h"

using namespace xolver;

TEST_CASE("model validator: constant UF accepts array arguments and rejects opaque Boolean results") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    ir.registerSort(1, SortKind::Int);
    ir.registerArraySort(2, 1, 1);
    const auto a = ir.add(TermExpr{Kind::Variable, 2, {}, Payload{std::string("a")}});
    const auto predicate = ir.add(TermExpr{Kind::UFApply, 0, {a}, Payload{std::string("p")}});
    ArithModelValidator::NumAssignment numbers;
    ArithModelValidator::BoolAssignment booleans;
    ArithModelValidator validator(ir, numbers, booleans);
    ArithModelValidator::FuncInterpMap functions;
    functions["p"].argSorts = {"(Array Int Int)"};
    functions["p"].retSort = "Bool";
    functions["p"].deflt = "true";
    validator.setFunctionInterps(&functions);
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Satisfied);
    functions["p"].deflt = "false";
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Violated);
    functions["p"].deflt = "@unresolved";
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Indeterminate);
}

TEST_CASE("model validator: array UF arguments use extensional values") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    ir.registerSort(1, SortKind::Int);
    ir.registerArraySort(2, 1, 1);
    auto a = ir.add(TermExpr{Kind::Variable, 2, {}, Payload{std::string("a")}});
    auto predicate = ir.add(TermExpr{Kind::UFApply, 0, {a}, Payload{std::string("p")}});
    ArithModelValidator::ArrayAssignment arrays, values;
    arrays["a"] = {"Int", "Int", "#n:0", {{"#n:1", "#n:2"}}};
    // Different order, repeated writes and redundant default stores describe
    // exactly the same array. Its value handle is unrelated to variable a.
    values["@array1"] = {"Int", "Int", "#n:0",
        {{"#n:2", "#n:0"}, {"#n:1", "#n:7"}, {"#n:1", "#n:2"}}};
    values["@array2"] = {"Int", "Int", "#n:1", {{"#n:1", "#n:2"}}};
    ArithModelValidator::TokenAssignment tokens;
    ArithModelValidator validator(ir, {}, {}, arrays, tokens);
    ArithModelValidator::FuncInterpMap functions;
    auto& f = functions["p"];
    f.argSorts = {"(Array Int Int)"}; f.retSort = "Bool"; f.deflt = "false";
    f.entries = {{{"@array1"}, "true"}, {{"@array2"}, "false"}};
    validator.setFunctionInterps(&functions, &values);
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Satisfied);
    f.entries[0].value = "false";
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Violated);
    f.entries[0].value = "true";
    values["@alias"] = arrays["a"];
    f.entries.push_back({{"@alias"}, "false"});
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Indeterminate);
    f.entries.pop_back();
    values.erase("@array1");
    f.deflt = "true";
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Indeterminate);
}

TEST_CASE("model validator: Boolean array domain ignores unreachable defaults") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    ir.registerSort(1, SortKind::Int);
    ir.registerArraySort(2, 0, 1);
    auto a = ir.add(TermExpr{Kind::Variable, 2, {}, Payload{std::string("a")}});
    auto predicate = ir.add(TermExpr{Kind::UFApply, 0, {a}, Payload{std::string("p")}});
    ArithModelValidator::ArrayAssignment arrays, values;
    arrays["a"] = {"Bool", "Int", "#n:0", {}};
    values["@other"] = {"Bool", "Int", "#n:1", {{"#b:0", "#n:0"}, {"#b:1", "#n:0"}}};
    ArithModelValidator::TokenAssignment tokens;
    ArithModelValidator validator(ir, {}, {}, arrays, tokens);
    ArithModelValidator::FuncInterpMap functions;
    functions["p"] = {{"(Array Bool Int)"}, "Bool", {{{"@other"}, "true"}}, "false"};
    validator.setFunctionInterps(&functions, &values);
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Satisfied);
    values["@other"].entries.pop_back();
    CHECK(validator.validate({predicate}) == ArithModelValidator::Verdict::Violated);
}

TEST_CASE("model validator: UF array result and mixed Boolean argument") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    ir.registerSort(1, SortKind::Int);
    ir.registerArraySort(2, 1, 1);
    auto yes = ir.add(TermExpr{Kind::ConstBool, 0, {}, Payload{true}});
    auto zero = ir.add(TermExpr{Kind::ConstInt, 1, {}, Payload{int64_t(0)}});
    auto result = ir.add(TermExpr{Kind::UFApply, 2, {yes}, Payload{std::string("f")}});
    auto read = ir.add(TermExpr{Kind::Select, 1, {result, zero}, {}});
    auto assertion = ir.add(TermExpr{Kind::Eq, 0, {read, zero}, {}});
    ArithModelValidator validator(ir, {}, {});
    ArithModelValidator::ArrayAssignment values;
    values["@result"] = {"Int", "Int", "#n:0", {}};
    ArithModelValidator::FuncInterpMap functions;
    functions["f"] = {{"Bool"}, "(Array Int Int)", {{{"#b:1"}, "@result"}}, ""};
    validator.setFunctionInterps(&functions, &values);
    CHECK(validator.validate({assertion}) == ArithModelValidator::Verdict::Satisfied);
    values["@result"].defaultVal = "#n:1";
    CHECK(validator.validate({assertion}) == ArithModelValidator::Verdict::Violated);
}
