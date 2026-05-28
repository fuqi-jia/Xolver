// Agent-1 regression locks for fixes that were lost/at-risk in merges:
//   1. LogicFeatureDetector must SKIP synthetic ("__"-prefixed) variables, e.g.
//      an Int-sorted ITE-lowering aux in a QF_LRA file, so it is not flagged
//      Int/Mixed -> false logic mismatch -> Unknown (the gasburner merge-casualty).
//      A GENUINE Int var in QF_LRA must still be flagged.
//   2. LraSolver::evalAtomAtModel evaluates a bound atom at the current simplex
//      point (the cb_decide / XOLVER_LRA_DECIDE feasibility heuristic core).
//   3. XOLVER_LRA_DECIDE must not change a verdict (sound regardless of value).

#include <doctest/doctest.h>
#include "expr/ir.h"
#include "expr/types.h"
#include "theory/core/LogicFeatureDetector.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/lra/LraSolver.h"
#include "util/RealValue.h"
#include "sat/SatSolver.h"
#include "xolver/Solver.h"
#include <cstdlib>
#include <fstream>
#include <filesystem>

using namespace xolver;

namespace {
// Minimal SatSolver so TheoryAtomRegistry::setContext is non-null (its
// observeIfNeeded dereferences sat_). addObservedVar is a no-op (default).
struct StubSat : SatSolver {
    SatVar next_ = 1;
    SatVar newVar() override { return next_++; }
    void addClause(const std::vector<SatLit>&) override {}
    SolveResult solve() override { return SolveResult::Unknown; }
    SolveResult solve(const std::vector<SatLit>&) override { return SolveResult::Unknown; }
    bool value(SatVar) const override { return false; }
};
} // namespace

namespace {

// Build an IR with Bool/Int/Real sorts registered. Returns the sort ids.
struct SortedIr {
    CoreIr ir;
    SortId boolS, intS, realS;
    SortedIr() {
        boolS = ir.allocateSortId(); ir.registerSort(boolS, SortKind::Bool); ir.setBoolSortId(boolS);
        intS  = ir.allocateSortId(); ir.registerSort(intS,  SortKind::Int);  ir.setIntSortId(intS);
        realS = ir.allocateSortId(); ir.registerSort(realS, SortKind::Real); ir.setRealSortId(realS);
    }
    // (= a b) as a bool assertion (the detector only inspects sorts).
    ExprId mkEqAssert(ExprId a, ExprId b) {
        CoreExpr e; e.kind = Kind::Eq; e.sort = boolS;
        e.children.push_back(a); e.children.push_back(b);
        ExprId id = ir.add(std::move(e));
        ir.addAssertion(id);
        return id;
    }
};

} // namespace

TEST_CASE("LogicFeatureDetector: synthetic Int aux is NOT flagged as user Int (gasburner lock)") {
    SortedIr s;
    // A real user var and a synthetic Int ITE-aux (name starts with "__").
    ExprId xReal   = s.ir.makeFreshVariable(s.realS, "x");
    ExprId synthInt = s.ir.makeFreshVariable(s.intS, "__nlc_ite");  // -> "__nlc_ite_0"
    s.mkEqAssert(xReal, synthInt);

    LogicFeatureDetector det(s.ir);
    LogicFeatures f = det.detect();
    CHECK(f.hasRealVar);
    CHECK_FALSE(f.hasIntVar);        // synthetic Int aux skipped
    CHECK_FALSE(f.hasMixedIntReal);  // => no QF_LRA logic mismatch
}

TEST_CASE("LogicFeatureDetector: genuine Int var IS flagged in a Real formula") {
    SortedIr s;
    ExprId yReal     = s.ir.makeFreshVariable(s.realS, "y");
    ExprId genuineInt = s.ir.makeFreshVariable(s.intS, "userInt");  // not "__"
    s.mkEqAssert(yReal, genuineInt);

    LogicFeatureDetector det(s.ir);
    LogicFeatures f = det.detect();
    CHECK(f.hasRealVar);
    CHECK(f.hasIntVar);
    CHECK(f.hasMixedIntReal);
}

TEST_CASE("LraSolver::evalAtomAtModel evaluates atoms at the simplex point") {
    StubSat stub;
    TheoryAtomRegistry reg;
    reg.setContext(&stub, nullptr);
    LraSolver lra;
    lra.setRegistry(&reg);

    LinearFormKey formX;
    formX.terms.push_back({"x", mpq_class(1)});

    // Atom A: x <= 3 (satVar 2), Atom B: x >= 10 (satVar 3) — same var, B unasserted.
    reg.registerParsedTheoryAtom(2, /*exprId*/ NullExpr, TheoryId::LRA,
                                 LinearAtomPayload{formX, Relation::Leq, RealValue::fromInt(3)});
    reg.registerParsedTheoryAtom(3, /*exprId*/ NullExpr, TheoryId::LRA,
                                 LinearAtomPayload{formX, Relation::Geq, RealValue::fromInt(10)});

    const TheoryAtomRecord* recA = reg.findBySatVar(2);
    REQUIRE(recA != nullptr);
    lra.assertLit(*recA, /*value*/ true, /*level*/ 0, SatLit::positive(2));

    TheoryLemmaDatabase db;
    auto r = lra.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Consistent);  // x<=3 is feasible

    // At the simplex model (x within (-inf,3], picked at 0), x<=3 holds and
    // x>=10 does not.
    auto evA = lra.evalAtomAtModel(2);
    auto evB = lra.evalAtomAtModel(3);
    REQUIRE(evA.has_value());
    REQUIRE(evB.has_value());
    CHECK(*evA == true);
    CHECK(*evB == false);
}

namespace {
std::string writeTmp(const std::string& content, const std::string& tag) {
    std::string path = std::filesystem::temp_directory_path() / ("xolver_a1lock_" + tag + ".smt2");
    std::ofstream ofs(path); ofs << content; return path;
}
Result solveWith(const std::string& smt2, const std::string& logic, bool decideOn) {
    if (decideOn) setenv("XOLVER_LRA_DECIDE", "1", 1); else unsetenv("XOLVER_LRA_DECIDE");
    std::string path = writeTmp(smt2, decideOn ? "on" : "off");
    Solver solver; solver.setLogic(logic);
    solver.parseFile(path);
    Result r = solver.checkSat();
    unsetenv("XOLVER_LRA_DECIDE");
    return r;
}
} // namespace

TEST_CASE("XOLVER_LRA_DECIDE: verdict unchanged (sound regardless of value)") {
    const std::string sat =
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n"
        "(assert (< x y))\n(assert (< y (+ x 5)))\n(check-sat)\n";
    const std::string unsat =
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n"
        "(assert (> x 1))\n(assert (< x 0))\n(check-sat)\n";

    CHECK(static_cast<int>(solveWith(sat, "QF_LRA", false)) == static_cast<int>(Result::Sat));
    CHECK(static_cast<int>(solveWith(sat, "QF_LRA", true))  == static_cast<int>(Result::Sat));
    CHECK(static_cast<int>(solveWith(unsat, "QF_LRA", false)) == static_cast<int>(Result::Unsat));
    CHECK(static_cast<int>(solveWith(unsat, "QF_LRA", true))  == static_cast<int>(Result::Unsat));
}
