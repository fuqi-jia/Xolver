// A model the independent validator cannot fully evaluate (Indeterminate — e.g.
// an uninterpreted function the validator has no interpretation for) must NOT
// escape as sat; it is downgraded to `unknown`. This only ever turns
// sat -> unknown, so it can never introduce a wrong answer.
#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include "applications/satisfiability/smt/qflra/LraSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <string>

using namespace xolver;

namespace {
Result solveStr(const std::string& smt, const std::string& tag) {
    std::string path = (std::filesystem::temp_directory_path() /
                        ("xolver_sv_" + tag + ".smt2")).string();
    { std::ofstream(path) << smt; }
    Solver s;
    REQUIRE(s.parseFile(path));
    return s.checkSat();
}
} // namespace

TEST_CASE("LRA model: delta materialization preserves ordinary and interface disequalities") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    const auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    const auto one = terms.add({Kind::ConstReal, 0, {}, Payload(std::string("1"))});
    SharedTermRegistry shared;
    shared.setNativeTerms(&terms);
    const auto sx = shared.getOrCreate(x, 0, "x", false);
    const auto sone = shared.getOrCreate(one, 0, "1", false);
    LraSolver solver;
    solver.setNativeTerms(&terms);
    solver.setSharedTermRegistry(&shared);
    TheoryLemmaDatabase lemmas;
    LinearFormKey form;
    form.terms.push_back({"x", mpq_class(1)});
    TheoryAtomRecord positive{1, TheoryId::LRA, false, NullExpr,
        LinearAtomPayload{form, Relation::Gt, RealValue::fromInt(0)}};
    solver.assertLit(positive, true, 0, SatLit::positive(1));
    REQUIRE(solver.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    SUBCASE("ordinary disequality") {
        TheoryAtomRecord different{2, TheoryId::LRA, false, NullExpr,
            LinearAtomPayload{form, Relation::Neq, RealValue::fromInt(1)}};
        solver.assertLit(different, true, 0, SatLit::positive(2));
    }
    SUBCASE("interface disequality") {
        REQUIRE(solver.assertInterfaceDisequality(sx, sone, SatLit::positive(2), 0).kind
                == TheoryCheckResult::Kind::Consistent);
    }
    REQUIRE(solver.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    const auto model = solver.getModel();
    REQUIRE(model.has_value());
    const auto value = model->numericAssignments.at("x").tryAsRational();
    REQUIRE(value.has_value());
    CHECK(*value > 0);
    CHECK(*value != 1);
    REQUIRE(solver.sharedTermArithValue(sx).has_value());
    CHECK(solver.sharedTermArithValue(sx)->tryAsRational() == value);
}

TEST_CASE("model validation: confirmable models stay sat") {
    // Pure boolean (values come from the SAT assignment, populated by the gate).
    CHECK(static_cast<int>(solveStr(
        "(declare-const p Bool)(assert (or p (not p)))(check-sat)\n", "bool"))
        == static_cast<int>(Result::Sat));
    // Pure boolean, forced value.
    CHECK(static_cast<int>(solveStr(
        "(declare-const p Bool)(assert p)(check-sat)\n", "p"))
        == static_cast<int>(Result::Sat));
    // Linear integer arithmetic (numeric model is positively evaluable).
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)(assert (> x 5))(check-sat)\n", "arith"))
        == static_cast<int>(Result::Sat));
    // Mixed bool + arith.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const p Bool)(declare-const x Int)"
        "(assert (and p (> x 5)))(check-sat)\n", "mix"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("NIA validate-sat floor (DEFAULT-ON): genuine NIA sat stays sat") {
    // No env flag: NIA (nonlinear integer) sat-validation is default-on
    // (invariant 1). A genuine NIA sat with a fully-evaluable integer model
    // (x in {2,3}) must stay sat — the integer model validates, so the floor
    // does NOT over-flip it.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_NIA)(declare-fun x () Int)"
        "(assert (and (> x 1) (< x 4) (>= (* x x) 4)))(check-sat)\n", "nia_sat"))
        == static_cast<int>(Result::Sat));
    // A pure-linear QF_LIA sat is not nonlinear, so the floor leaves it alone.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-fun y () Int)(assert (> y 5))(check-sat)\n", "lia_sat"))
        == static_cast<int>(Result::Sat));
}

TEST_CASE("model validation: unsat is unaffected") {
    // The gate only ever touches a Sat verdict; unsat passes through.
    CHECK(static_cast<int>(solveStr(
        "(set-logic QF_LIA)(declare-const x Int)"
        "(assert (and (> x 5) (< x 2)))(check-sat)\n", "unsat"))
        == static_cast<int>(Result::Unsat));
}
