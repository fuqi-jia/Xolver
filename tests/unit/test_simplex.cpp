#include <doctest/doctest.h>
#include "theory/arith/lra/SimplexSolver.h"
#include "expr/ir.h"

using namespace nlcolver;

TEST_CASE("SimplexSolver: single variable bound conflict") {
    CoreIr ir;

    // x < 0
    ExprId x = ir.add(CoreExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    ExprId zero = ir.add(CoreExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    ExprId lt0 = ir.add(CoreExpr{Kind::Lt, 0, {x, zero}, {}});

    // x = 0
    ExprId eq0 = ir.add(CoreExpr{Kind::Eq, 0, {x, zero}, {}});

    SimplexSolver solver;
    solver.push();

    // assert x < 0 (satVar 1)
    solver.assertLit({1, lt0}, true, ir);
    auto r1 = solver.check(ir);
    CHECK(r1.kind == TheoryCheckResult::Kind::Consistent);

    // assert x = 0 (satVar 2)
    solver.assertLit({2, eq0}, true, ir);
    auto r2 = solver.check(ir);
    CHECK(r2.kind == TheoryCheckResult::Kind::Conflict);

    CHECK(r2.conflictOpt.has_value());
    CHECK(r2.conflictOpt->clause.size() == 2);
}
