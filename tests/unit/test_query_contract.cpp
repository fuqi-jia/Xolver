#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "ir/NativeTerms.h"
#include "base/EnvParam.h"
#include "evidence/ModelValidator.h"
#include "base/MpqUtils.h"
#include "base/SolveClock.h"
#include <cstdlib>
#include <limits>
#include <optional>
#include <stdexcept>
#include <thread>

using namespace xolver;
namespace {
struct QueryEnv {
    std::string name;
    std::optional<std::string> saved;
    QueryEnv(const char* n, const char* value) : name(n) {
        if (auto p = std::getenv(n)) saved = p;
        setenv(n, value, 1);
    }
    ~QueryEnv() {
        if (saved) setenv(name.c_str(), saved->c_str(), 1);
        else unsetenv(name.c_str());
    }
};
Term op(Solver& s, Kind k, std::initializer_list<Term> args) {
    return s.mkOp(static_cast<uint32_t>(k), args);
}
}

TEST_CASE("query contract: handle sentinels agree with NativeTerms") {
    CHECK(Term{}.id() == NullExpr);
    CHECK(Sort{}.id() == NullSort);
    CHECK(Term{}.isNull());
    CHECK(Sort{}.isNull());
    CHECK_FALSE(Term{0}.isNull());
    CHECK_FALSE(Sort{0}.isNull());
    OptionValue v;
    CHECK(v.kind == OptionValue::Bool);
    CHECK_FALSE(v.b);
    OptionValue text("checked");
    CHECK(text.kind == OptionValue::String);
    CHECK(text.s == "checked");
}

TEST_CASE("query contract: push before allocating terms and pop underflow") {
    Solver s;
    s.push();
    s.assertFormula(s.mkBool(false));
    CHECK((s.checkSat() == Result::Unsat));
    s.pop();
    CHECK((s.checkSat() == Result::Sat));
    CHECK_THROWS_AS(s.pop(), std::invalid_argument);
    CHECK_THROWS_AS(s.assertFormula(Term{}), std::invalid_argument);
    CHECK_THROWS_AS(s.assertFormula(s.mkInt(1)), std::invalid_argument);
}

TEST_CASE("query contract: handles cannot cross solvers or survive reset") {
    Solver a, b;
    auto sort = a.intSort();
    auto t = a.mkBool(true);
    CHECK_THROWS_AS(b.assertFormula(t), std::invalid_argument);
    CHECK_THROWS_AS(b.mkConst(sort, "x"), std::invalid_argument);
    CHECK_THROWS_AS(op(b, Kind::Not, {t}), std::invalid_argument);
    a.reset();
    a.mkBool(false); // Reuse the same dense ExprId in the new context.
    CHECK_THROWS_AS(a.assertFormula(t), std::invalid_argument);
    CHECK_THROWS_AS(a.getValue(t), std::invalid_argument);
}

TEST_CASE("query contract: preprocessing preserves original roots across queries") {
    Solver s;
    s.setLogic("QF_LIA");
    auto x = s.mkConst(s.intSort(), "x");
    s.assertFormula(op(s, Kind::Eq, {x, s.mkInt(42)}));
    for (int round = 0; round < 2; ++round) {
        REQUIRE((s.checkSat() == Result::Sat));
        auto m = s.getModel();
        REQUIRE(m.getValue(x.id()));
        CHECK(*m.getValue(x.id()) == "42");
        CHECK(s.validateModel() == Solver::ModelValidation::Satisfied);
    }
    s.push();
    s.assertFormula(op(s, Kind::Eq, {x, s.mkInt(43)}));
    CHECK((s.checkSat() == Result::Unsat));
    CHECK(s.getModel().isEmpty());
    s.pop();
    REQUIRE((s.checkSat() == Result::Sat));
    CHECK(s.validateModel() == Solver::ModelValidation::Satisfied);
}

TEST_CASE("query contract: assumptions survive lowering and candidate search") {
    Solver s;
    s.setLogic("QF_NIA");
    auto x = s.mkConst(s.intSort(), "x");
    auto square = op(s, Kind::Mul, {x, x});
    auto impossible = op(s, Kind::Eq, {square, s.mkInt(2)});
    s.assertFormula(s.mkBool(true));
    CHECK((s.checkSatAssuming({impossible}) == Result::Unsat));
    CHECK((s.checkSat() == Result::Sat));
    CHECK(s.getUnsatCore().empty());
    CHECK_THROWS_AS(s.checkSatAssuming({x}), std::invalid_argument);

    Solver empty;
    auto f = empty.mkBool(false);
    CHECK((empty.checkSatAssuming({f}) == Result::Unsat));
    CHECK((empty.checkSat() == Result::Sat));
}

TEST_CASE("query contract: SAT evidence is three valued") {
    Solver s;
    CHECK(s.validateModel() == Solver::ModelValidation::Indeterminate);
    auto p = s.mkConst(s.boolSort(), "p");
    s.assertFormula(p);
    REQUIRE((s.checkSat() == Result::Sat));
    CHECK(s.validateModel() == Solver::ModelValidation::Satisfied);
    s.assertFormula(s.mkBool(false));
    CHECK(s.validateModel() == Solver::ModelValidation::Indeterminate);
    CHECK((s.checkSat() == Result::Unsat));
    CHECK(s.validateModel() == Solver::ModelValidation::Indeterminate);
}

TEST_CASE("query contract: exact literals and symbol identity") {
    Solver s;
    s.setLogic("QF_LIA");
    auto x = s.mkConst(s.intSort(), "x");
    CHECK(x == s.mkConst(s.intSort(), "x"));
    CHECK_THROWS_AS(s.mkConst(s.realSort(), "x"), std::invalid_argument);
    const std::string big = "100000000000000000000000000000000000000000000000000000000001";
    s.assertFormula(op(s, Kind::Eq, {x, s.mkInt(big)}));
    REQUIRE((s.checkSat() == Result::Sat));
    CHECK(s.validateModel() == Solver::ModelValidation::Satisfied);
    auto value = s.getValue(x);
    CHECK_FALSE(value.isNull());
    CHECK(s.getModel().getValue(x.id()) != nullptr);
    CHECK_THROWS_AS(s.mkReal("1/0"), std::invalid_argument);
    CHECK(mpqFromString("2/4") == mpq_class(1, 2));
    CHECK(mpqFromString("-0.125") == mpq_class(-1, 8));
    CHECK(mpqFromString("1.25e-2") == mpq_class(1, 80));
    CHECK(mpqFromString("2/-4") == mpq_class(-1, 2));
    CHECK_THROWS_AS(mpqFromString("1e2garbage"), std::invalid_argument);
}

TEST_CASE("query contract: independent threads cannot end each other's deadlines") {
    wall::beginSolve(60000);
    std::thread other([] { wall::endSolve(); });
    other.join();
    CHECK(wall::hasDeadline());
    CHECK(wall::remainingMs() > 0);
    wall::endSolve();
}

TEST_CASE("query contract: reserved-looking user names do not hide integer sorts") {
    Solver s;
    s.setLogic("QF_LRA");
    auto x = s.mkConst(s.intSort(), "__user_integer");
    s.assertFormula(op(s, Kind::Eq, {op(s, Kind::Mul, {s.mkInt(2), x}), s.mkInt(1)}));
    CHECK((s.checkSat() != Result::Sat));
}

TEST_CASE("query contract: scaled resource budgets saturate machine limits") {
    // Also run alone with XOLVER_WALLCLOCK_SCALE=1 to exercise the enabled path.
    const long limit = std::numeric_limits<long>::max();
    wall::beginSolve(limit);
    CHECK(wall::scaledCount(limit, 1, limit) == limit);
    CHECK(wall::scaledCount(7, 1, limit) >= 7);
    CHECK(wall::scaledBudgetMs(limit, std::numeric_limits<int>::max(), 1) > 0);
    wall::endSolve();
}

TEST_CASE("query contract: callback exceptions unwind query resources") {
    struct Throwing : Propagator {
        void onSetup(const std::vector<ObservedAtom>&) override {
            throw std::runtime_error("test callback failure");
        }
    } callback;
    Solver s;
    auto p = s.mkConst(s.boolSort(), "p");
    auto q = s.mkConst(s.boolSort(), "q");
    s.assertFormula(op(s, Kind::Or, {p, q}));
    s.setPropagator(&callback);
    CHECK((s.checkSat() == Result::Unknown));
    s.clearPropagator();
    CHECK((s.checkSat() == Result::Sat));
}

TEST_CASE("query contract: budgets reject overflow, suffixes and nonfinite values") {
    constexpr const char* name = "XOLVER_TEST_QUERY_BUDGET";
    for (auto bad : {"17garbage", "999999999999999999999999999999999999"}) {
        QueryEnv e(name, bad);
        CHECK(env::paramLong(name, 13) == 13);
        CHECK(env::paramInt(name, 13) == 13);
    }
    {
        QueryEnv e(name, "2147483648");
        CHECK(env::paramInt(name, 13) == 13);
    }
    for (auto bad : {"nan", "inf", "1e9999", "2.5ms"}) {
        QueryEnv e(name, bad);
        CHECK(env::paramDouble(name, 1.25) == 1.25);
    }
    QueryEnv e(name, " 17 \t");
    CHECK(env::paramInt(name, 13) == 17);
}

TEST_CASE("Boolean validator: unsupported formulas cannot certify under negation") {
    NativeTerms ir;
    ir.registerSort(0, SortKind::Bool);
    auto unknown = ir.add(TermExpr{Kind::Unknown, 0, {}, {}});
    auto neg = ir.add(TermExpr{Kind::Not, 0, {unknown}, {}});
    auto twice = ir.add(TermExpr{Kind::Not, 0, {neg}, {}});
    ModelValidator validator;
    CHECK_FALSE(validator.eval(unknown, ir, {}));
    CHECK_FALSE(validator.eval(neg, ir, {}));
    CHECK_FALSE(validator.eval(twice, ir, {}));
    CHECK_FALSE(validator.eval(NullExpr, ir, {}));
}
