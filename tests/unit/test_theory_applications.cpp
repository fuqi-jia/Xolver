#include "applications/smt/Solver.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace {
SolverAnswer solve(const std::string &source) {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    if (!parser.parseStr("(set-logic ALL)" + source))
        throw std::runtime_error("theory test parse error");
    applications::smt::Solver solver;
    return solver.solve({parser.getAssertions(), {}, {}, {}});
}
void check(const std::string &source, Result expected) {
    auto answer = solve(source);
    INFO(source);
    INFO(answer.reason);
    CHECK((answer.result == expected));
}
} // namespace
TEST_CASE("theory applications: finite UF and extensional arrays") {
    check("(declare-fun f ((_ BitVec 4)) (_ BitVec 4))(declare-const x (_ BitVec 4))(assert (= x "
          "#x1))(assert (distinct (f x) (f #x1)))",
          Result::Unsat);
    auto uf = solve("(declare-fun f ((_ BitVec 4)) (_ BitVec 4))(assert (= (f #x0) #x1))(assert (= "
                    "(f #x1) #x2))");
    REQUIRE((uf.result == Result::Sat));
    REQUIRE(uf.model);
    CHECK(uf.model->functionInterps.at("f").entries.size() == 2);
    check("(declare-const a (Array (_ BitVec 2) (_ BitVec 4)))(declare-const i (_ BitVec "
          "2))(assert (distinct (select (store a i #xf) i) #xf))",
          Result::Unsat);
    check("(declare-const a (Array (_ BitVec 2) (_ BitVec 4)))(declare-const b (Array (_ BitVec 2) "
          "(_ BitVec 4)))(assert (= a b))(assert (distinct (select a #b01) (select b #b01)))",
          Result::Unsat);
    check("(declare-const a (Array (_ BitVec 2) (_ BitVec 4)))(assert (distinct a ((as const "
          "(Array (_ BitVec 2) (_ BitVec 4))) #x0)))",
          Result::Sat);
    check("(declare-const a (Array (_ BitVec 64) (_ BitVec 4)))(assert (= (select a (_ bv0 64)) "
          "#xf))",
          Result::Unknown);
}
TEST_CASE("theory applications: floating-point value semantics") {
    check("(assert (= (_ +zero 8 24) (_ -zero 8 24)))", Result::Unsat);
    check("(assert (fp.eq (_ +zero 8 24) (_ -zero 8 24)))", Result::Sat);
    check("(assert (fp.eq (_ NaN 8 24) (_ NaN 8 24)))", Result::Unsat);
    check("(assert (= (fp #b0 #b11 #b01) (fp #b1 #b11 #b10)))", Result::Sat);
    check("(declare-const x (_ FloatingPoint 8 24))(assert (fp.isNaN x))(assert (fp.isNegative x))",
          Result::Unsat);
    check("(declare-const x (_ FloatingPoint 8 24))(assert (fp.isSubnormal x))(assert "
          "(fp.isPositive x))",
          Result::Sat);
    check("(declare-const x (_ FloatingPoint 8 24))(assert (fp.lt x (fp.neg x)))(assert "
          "(fp.isPositive x))",
          Result::Unsat);
    check("(declare-const x (_ BitVec 32))(assert (fp.isInfinite ((_ to_fp 8 24) x)))",
          Result::Sat);
    check("(declare-const x (_ FloatingPoint 8 24))(assert (fp.eq (fp.add RNE x x) x))",
          Result::Unknown);
}
TEST_CASE("theory applications: Unicode strings, regex and arithmetic") {
    check(R"((declare-const s String)(assert (= s "abc"))(assert (= (str.len s) 3)))", Result::Sat);
    check(R"((declare-const s String)(assert (= s "a"))(assert (= s "b")))", Result::Unsat);
    check(
        R"((declare-const s String)(declare-const t String)(assert (= s t))(assert (distinct s t)))",
        Result::Unsat);
    check(R"((declare-const s String)(assert (str.contains s "abc")))", Result::Sat);
    check(R"((assert (= (str.len "\u{1f600}") 1)))", Result::Sat);
    check(R"((assert (= (str.substr "abc" (- 1) 2) "")))", Result::Sat);
    check(R"((assert (= (str.indexof "abc" "" 3) 3)))", Result::Sat);
    check(R"((assert (= (str.to_int "12x") (- 1))))", Result::Sat);
    check(R"((assert (str.in_re "abba" (re.* (re.union (str.to_re "a") (str.to_re "b"))))))",
          Result::Sat);
    check(R"((assert (str.in_re "abc" (re.* (str.to_re "a")))))", Result::Unsat);
    check(
        R"((declare-const s String)(declare-const n Int)(assert (= s "ab"))(assert (= n (str.len s)))(assert (> n 3)))",
        Result::Unsat);
    check(R"((declare-const s String)(assert (= (str.len s) 1000)))", Result::Unknown);
}
TEST_CASE("theory applications: compound sorts cannot hide unsupported finite domains") {
    for (const auto &source :
         {"(declare-const a (Array Bool RoundingMode))(declare-const b (Array Bool "
          "RoundingMode))(assert (distinct a b))",
          "(declare-datatype Box ((box (value (_ FloatingPoint 2 3)))))"
          "(declare-const a Box)(declare-const b Box)(assert (distinct a b))",
          "(declare-datatype Box ((box (value (_ BitVec 2)))))"
          "(declare-const a Box)(declare-const b Box)(assert (distinct a b))"}) {
        SOMTParser::Parser parser;
        preserveNativeTheories(*parser.getOptions());
        REQUIRE(parser.parseStr(std::string("(set-logic ALL)") + source));
        bool groundCalled = false;
        applications::smt::Solver solver([&](const applications::smt::Problem &) {
            groundCalled = true;
            SolverAnswer result;
            result.result = Result::Sat;
            return result;
        });
        auto result = solver.solve({parser.getAssertions(), {}, {}, {}});
        INFO(source);
        CHECK_FALSE(groundCalled);
        CHECK((result.result == Result::Unknown));
        CHECK_FALSE(result.reason.empty());
    }
}
