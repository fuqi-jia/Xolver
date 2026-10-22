#include <doctest/doctest.h>
#include "search/candidate/CandidateModelSearch.h"
#include "evidence/ArithModelValidator.h"

using namespace xolver;

namespace {
struct CandidateFixture {
    NativeTerms ir;
    SortId boolean, integer;
    CandidateFixture() {
        boolean = ir.allocateSortId();
        ir.registerSort(boolean, SortKind::Bool);
        ir.setBoolSortId(boolean);
        integer = ir.allocateSortId();
        ir.registerSort(integer, SortKind::Int);
        ir.setIntSortId(integer);
    }
    ExprId number(int64_t n) {
        return ir.add(TermExpr{Kind::ConstInt, integer, {}, Payload(n)});
    }
    ExprId apply(ExprId arg) {
        TermExpr term;
        term.kind = Kind::UFApply;
        term.sort = integer;
        term.payload = Payload(std::string("f"));
        term.children.push_back(arg);
        return ir.add(std::move(term));
    }
    void equal(ExprId lhs, ExprId rhs) {
        TermExpr term;
        term.kind = Kind::Eq;
        term.sort = boolean;
        term.children.push_back(lhs);
        term.children.push_back(rhs);
        ir.addAssertion(ir.add(std::move(term)));
    }
};
}

TEST_CASE("CandidateModelSearch: default UF search emits an independently valid function table") {
    CandidateFixture f;
    f.equal(f.apply(f.number(0)), f.number(7));
    f.equal(f.apply(f.number(1)), f.number(9));
    CandidateModelSearch search(f.ir, "QF_UFLIA");
    auto result = search.run();
    REQUIRE(result.found);
    REQUIRE(result.model.functionInterps.count("f") == 1);
    ArithModelValidator::NumAssignment numbers;
    ArithModelValidator::BoolAssignment booleans;
    ArithModelValidator validator(f.ir, numbers, booleans);
    validator.setFunctionInterps(&result.model.functionInterps);
    CHECK(validator.validate(f.ir.assertions()) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("CandidateModelSearch: equal evaluated arguments cannot have unequal function values") {
    CandidateFixture f;
    auto x = f.ir.add(TermExpr{Kind::Variable, f.integer, {}, Payload(std::string("x"))});
    f.equal(x, f.number(0));
    f.equal(f.apply(x), f.number(1));
    f.equal(f.apply(f.number(0)), f.number(2));
    CandidateModelSearch search(f.ir, "QF_UFLIA");
    CHECK_FALSE(search.run().found);
}

TEST_CASE("CandidateModelSearch: unsupported UF arguments cannot yield a partial model") {
    CandidateFixture f;
    auto truth = f.ir.add(TermExpr{Kind::ConstBool, f.boolean, {}, Payload(true)});
    f.equal(f.apply(truth), f.number(7));
    CandidateModelSearch search(f.ir, "QF_UFLIA");
    // This numeric candidate search does not yet model Boolean arguments.
    // A slot value alone must not count as a complete function interpretation.
    CHECK_FALSE(search.run().found);
}
