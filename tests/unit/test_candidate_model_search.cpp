#include <doctest/doctest.h>
#include "search/candidate/CandidateModelSearch.h"
#include "evidence/ArithModelValidator.h"
#include "ir/RequiredFacts.h"

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
    ExprId variable() {
        return ir.add({Kind::Variable, integer, {}, Payload(std::string("x"))});
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
    void check(const CandidateModelSearch::Result& result) {
        REQUIRE(result.found);
        ArithModelValidator::NumAssignment numbers;
        ArithModelValidator::BoolAssignment booleans;
        for (const auto& [name, value] : result.model.assignments)
            numbers[name] = mpq_class(value);
        ArithModelValidator validator(ir, numbers, booleans);
        validator.setFunctionInterps(&result.model.functionInterps);
        CHECK(validator.validate(ir.assertions()) == ArithModelValidator::Verdict::Satisfied);
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

TEST_CASE("CandidateModelSearch: integer division validates Euclidean quotients") {
    struct Example { int numerator, divisor, quotient; };
    for (const auto example : {Example{3, 2, 1}, Example{3, -2, -1},
                               Example{-3, 2, -2}, Example{-3, -2, 2}}) {
        CAPTURE(example.numerator); CAPTURE(example.divisor);
        for (const bool equality : {true, false}) {
            CAPTURE(equality);
            CandidateFixture f;
            const auto x = f.variable();
            f.equal(x, f.number(example.numerator));
            const auto quotient = f.ir.add({Kind::Div, f.integer,
                                            {x, f.number(example.divisor)}, {}});
            f.ir.addAssertion(f.ir.add({equality ? Kind::Eq : Kind::Distinct, f.boolean,
                                       {quotient, f.number(example.quotient)}, {}}));
            const auto result = CandidateModelSearch(f.ir, "QF_LIA").run();
            if (equality) f.check(result);
            else CHECK_FALSE(result.found);
        }
    }
    CandidateFixture real;
    const auto sort = real.ir.allocateSortId();
    real.ir.registerSort(sort, SortKind::Real);
    auto number = [&](const std::string& value) {
        return real.ir.add({Kind::ConstReal, sort, {}, Payload(value)});
    };
    const auto x = real.ir.add({Kind::Variable, sort, {}, Payload(std::string("x"))});
    real.equal(x, number("3"));
    real.equal(real.ir.add({Kind::Div, sort, {x, number("2")}, {}}), number("3/2"));
    real.check(CandidateModelSearch(real.ir, "QF_LRA").run());
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

TEST_CASE("Candidate evaluation scopes: rejected candidates cannot retain numeric values") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto square = f.ir.add({Kind::Mul, f.integer, {x, x}, {}});
    f.equal(square, f.number(4));
    f.equal(f.ir.add({Kind::Add, f.integer, {square, x}, {}}), f.number(6));
    f.check(CandidateModelSearch(f.ir, "QF_NIA").run());
}

TEST_CASE("Candidate evaluation scopes: contradictory shared assertions never accept") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto square = f.ir.add({Kind::Mul, f.integer, {x, x}, {}});
    f.equal(square, f.number(1));
    f.equal(square, f.number(4));
    CHECK_FALSE(CandidateModelSearch(f.ir, "QF_NIA").run().found);
}

TEST_CASE("Candidate evaluation scopes: nested UF derivation invalidates updated slots") {
    CandidateFixture f;
    const auto x = f.variable();
    f.equal(f.apply(f.number(0)), f.number(1));
    f.equal(f.apply(f.number(1)), f.number(2));
    f.equal(f.apply(f.number(2)), f.number(3));
    f.equal(f.ir.add({Kind::Mul, f.integer, {x, x}, {}}), f.number(1));
    f.equal(f.apply(f.apply(x)), f.number(3));
    f.check(CandidateModelSearch(f.ir, "QF_UFNIA").run());
}

TEST_CASE("Candidate evaluation scopes: shared assertion DAG preserves a complete witness") {
    CandidateFixture f;
    const auto zero = f.number(0);
    auto sum = f.variable();
    for (int i = 0; i < 64; ++i) sum = f.ir.add({Kind::Add, f.integer, {sum, zero}, {}});
    for (int i = 0; i < 32; ++i) f.equal(sum, zero);
    f.check(CandidateModelSearch(f.ir, "QF_LIA").run());
}

TEST_CASE("Candidate definitions: numeric variables can take derived values outside the enumeration grid") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto y = f.ir.add({Kind::Variable, f.integer, {}, Payload(std::string("y"))});
    f.equal(x, f.number(0));
    f.equal(y, f.ir.add({Kind::Add, f.integer, {x, f.number(100003)}, {}}));
    const auto result = CandidateModelSearch(f.ir, "QF_LIA").run();
    f.check(result);
    CHECK(result.model.assignments.at("y") == "100003");
}

TEST_CASE("Candidate definitions: dependent function results are completed in dependency order") {
    CandidateFixture f;
    const auto x = f.variable();
    f.equal(x, f.number(0));
    auto value = x;
    for (int i = 0; i < 12; ++i) {
        const auto app = f.apply(f.number(i));
        f.equal(app, f.ir.add({Kind::Add, f.integer, {value, f.number(100003)}, {}}));
        value = app;
    }
    f.check(CandidateModelSearch(f.ir, "QF_UFLIA").run());
}

TEST_CASE("Candidate definitions: completion preserves exact rational function values") {
    CandidateFixture f;
    const auto real = f.ir.allocateSortId();
    f.ir.registerSort(real, SortKind::Real);
    f.ir.setRealSortId(real);
    const auto x = f.ir.add({Kind::Variable, real, {}, Payload(std::string("r"))});
    const auto fraction = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("100003/7"))});
    const auto zero = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("0"))});
    const auto app = f.ir.add({Kind::UFApply, real, {x}, Payload(std::string("g"))});
    f.equal(x, zero);
    f.equal(app, f.ir.add({Kind::Add, real, {x, fraction}, {}}));
    const auto result = CandidateModelSearch(f.ir, "QF_UFLRA").run();
    f.check(result);
    REQUIRE(result.model.functionInterps.count("g") == 1);
    CHECK(result.model.functionInterps.at("g").entries.at(0).value == "100003/7");
}

TEST_CASE("Candidate definitions: cyclic equations retain a searchable witness") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto y = f.ir.add({Kind::Variable, f.integer, {}, Payload(std::string("y"))});
    f.equal(x, f.ir.add({Kind::Add, f.integer, {y, f.number(1)}, {}}));
    f.equal(y, f.ir.add({Kind::Sub, f.integer, {x, f.number(1)}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_LIA").run());
}

TEST_CASE("Candidate definitions: conflicting completed equations never bypass validation") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto app = f.apply(x);
    f.equal(app, f.ir.add({Kind::Add, f.integer, {x, f.number(100003)}, {}}));
    f.equal(app, f.ir.add({Kind::Add, f.integer, {x, f.number(100004)}, {}}));
    CHECK_FALSE(CandidateModelSearch(f.ir, "QF_UFLIA").run().found);
}

TEST_CASE("Candidate definitions: disjunctive equations do not become unconditional assignments") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto app = f.apply(x);
    const auto other = f.ir.add({Kind::Eq, f.boolean, {app, f.number(100003)}, {}});
    const auto same = f.ir.add({Kind::Eq, f.boolean, {app, f.number(0)}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Or, f.boolean, {other, same}, {}}));
    f.equal(app, f.number(0));
    f.check(CandidateModelSearch(f.ir, "QF_UFLIA").run());
}

TEST_CASE("Candidate definitions: assertion overrides exclude inactive conflicting definitions") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto app = f.apply(x);
    f.equal(app, f.ir.add({Kind::Add, f.integer, {x, f.number(100003)}, {}}));
    CandidateModelSearch::Config config;
    config.assertionRootsOverride = f.ir.assertions();
    f.equal(app, f.ir.add({Kind::Add, f.integer, {x, f.number(100004)}, {}}));
    const auto result = CandidateModelSearch(f.ir, "QF_UFLIA", config).run();
    REQUIRE(result.found);
    ArithModelValidator::NumAssignment numbers;
    ArithModelValidator::BoolAssignment booleans;
    for (const auto& [name, value] : result.model.assignments) numbers[name] = mpq_class(value);
    ArithModelValidator validator(f.ir, numbers, booleans);
    validator.setFunctionInterps(&result.model.functionInterps);
    CHECK(validator.validate(config.assertionRootsOverride) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("Candidate definitions: negated implication exposes a required numeric definition") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto app = f.apply(x);
    const auto value = f.ir.add({Kind::Add, f.integer, {x, f.number(100003)}, {}});
    const auto equation = f.ir.add({Kind::Eq, f.boolean, {app, value}, {}});
    const auto falsity = f.ir.add({Kind::ConstBool, f.boolean, {}, Payload(false)});
    const auto implication = f.ir.add({Kind::Implies, f.boolean, {equation, falsity}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Not, f.boolean, {implication}, {}}));
    f.equal(x, f.number(0));
    f.check(CandidateModelSearch(f.ir, "QF_UFLIA").run());
}

TEST_CASE("Required facts: shared expressions retain both required polarities") {
    CandidateFixture f;
    const auto equation = f.ir.add({Kind::Eq, f.boolean, {f.variable(), f.number(0)}, {}});
    const auto negative = f.ir.add({Kind::Not, f.boolean, {equation}, {}});
    const auto falsity = f.ir.add({Kind::ConstBool, f.boolean, {}, Payload(false)});
    const auto disjunction = f.ir.add({Kind::Or, f.boolean, {negative, falsity}, {}});
    const auto positive = f.ir.add({Kind::Not, f.boolean, {disjunction}, {}});
    const std::vector<ExprId> roots{positive, negative, positive};
    const auto facts = requiredFacts(f.ir, roots);
    size_t requiredTrue = 0, requiredFalse = 0;
    for (const auto& fact : facts) {
        if (fact.expression != equation) continue;
        if (fact.positive) ++requiredTrue;
        else ++requiredFalse;
    }
    CHECK(requiredTrue == 1);
    CHECK(requiredFalse == 1);
}

TEST_CASE("Candidate domains: a pinned function point leaves other integer results free") {
    CandidateFixture f;
    f.equal(f.apply(f.number(0)), f.number(1));
    const auto other = f.apply(f.number(1));
    const auto shifted = f.ir.add({Kind::Add, f.integer, {other, f.number(1)}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Gt, f.boolean, {shifted, f.number(9)}, {}}));
    f.ir.addAssertion(f.ir.add({Kind::Lt, f.boolean, {shifted, f.number(11)}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_UFLIA").run());
}

TEST_CASE("Candidate domains: a pinned function point leaves other rational results free") {
    CandidateFixture f;
    const auto real = f.ir.allocateSortId();
    f.ir.registerSort(real, SortKind::Real);
    f.ir.setRealSortId(real);
    const auto fixed = f.ir.add({Kind::UFApply, real, {f.number(0)}, Payload(std::string("g"))});
    const auto other = f.ir.add({Kind::UFApply, real, {f.number(1)}, Payload(std::string("g"))});
    const auto one = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("1"))});
    const auto lower = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("5/2"))});
    const auto upper = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("11/4"))});
    f.equal(fixed, one);
    const auto shifted = f.ir.add({Kind::Add, real, {other, one}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Gt, f.boolean, {shifted, lower}, {}}));
    f.ir.addAssertion(f.ir.add({Kind::Lt, f.boolean, {shifted, upper}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_UFLRA").run());
}

TEST_CASE("Candidate projection: dependent function results do not consume independent dimensions") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto square = f.ir.add({Kind::Mul, f.integer, {x, x}, {}});
    f.equal(square, f.number(81));
    const auto value = f.ir.add({Kind::Add, f.integer, {x, f.number(100003)}, {}});
    for (int i = 0; i < 12; ++i) f.equal(f.apply(f.number(i)), value);
    f.check(CandidateModelSearch(f.ir, "QF_UFNIA").run());
}

TEST_CASE("Candidate boundaries: negated comparisons expose large integer endpoints") {
    CandidateFixture f;
    const auto x = f.variable();
    const auto below = f.ir.add({Kind::Leq, f.boolean, {x, f.number(100003)}, {}});
    const auto above = f.ir.add({Kind::Geq, f.boolean, {x, f.number(100005)}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Not, f.boolean, {below}, {}}));
    f.ir.addAssertion(f.ir.add({Kind::Not, f.boolean, {above}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_LIA").run());
}

TEST_CASE("Candidate boundaries: a narrow required rational interval has an exact interior witness") {
    CandidateFixture f;
    const auto real = f.ir.allocateSortId();
    f.ir.registerSort(real, SortKind::Real);
    f.ir.setRealSortId(real);
    const auto x = f.ir.add({Kind::Variable, real, {}, Payload(std::string("r"))});
    const auto lower = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("100003/7"))});
    const auto upper = f.ir.add({Kind::ConstReal, real, {}, Payload(std::string("100004/7"))});
    const auto below = f.ir.add({Kind::Leq, f.boolean, {x, lower}, {}});
    const auto above = f.ir.add({Kind::Geq, f.boolean, {x, upper}, {}});
    const auto outside = f.ir.add({Kind::Or, f.boolean, {below, above}, {}});
    f.ir.addAssertion(f.ir.add({Kind::Not, f.boolean, {outside}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_LRA").run());
}

TEST_CASE("Candidate boundaries: numeric application bounds construct out-of-grid function values") {
    CandidateFixture f;
    const auto value = f.apply(f.number(0));
    f.ir.addAssertion(f.ir.add({Kind::Gt, f.boolean, {value, f.number(100003)}, {}}));
    f.ir.addAssertion(f.ir.add({Kind::Lt, f.boolean, {value, f.number(100005)}, {}}));
    f.check(CandidateModelSearch(f.ir, "QF_UFLIA").run());
}

TEST_CASE("Candidate boundaries: an empty open integer interval rejects rational interior candidates") {
    CandidateFixture f;
    const auto x = f.variable();
    f.ir.addAssertion(f.ir.add({Kind::Gt, f.boolean, {x, f.number(0)}, {}}));
    f.ir.addAssertion(f.ir.add({Kind::Lt, f.boolean, {x, f.number(1)}, {}}));
    CHECK_FALSE(CandidateModelSearch(f.ir, "QF_LIA").run().found);
}
