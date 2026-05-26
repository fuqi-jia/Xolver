#include <doctest/doctest.h>
#include "theory/combination/CareGraph.h"
#include "theory/combination/SharedTermRegistry.h"
#include "expr/ir.h"

using namespace zolver;

namespace {

ExprId addVar(CoreIr& ir, SortId sort, const std::string& name) {
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = sort;
    e.payload.value = name;
    return ir.add(e);
}

ExprId addConstInt(CoreIr& ir, SortId sort, int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = sort;
    e.payload.value = v;
    return ir.add(e);
}

ExprId addNode(CoreIr& ir, Kind k, SortId sort, std::initializer_list<ExprId> kids,
               const std::string& fnName = "") {
    CoreExpr e;
    e.kind = k;
    e.sort = sort;
    for (ExprId c : kids) e.children.push_back(c);
    if (!fnName.empty()) e.payload.value = fnName;
    return ir.add(e);
}

} // namespace

TEST_CASE("CareGraph: only inference-bearing operands are care-relevant") {
    CoreIr ir;
    const SortId intSort = 1, arrSort = 2, boolSort = 3;

    ExprId x   = addVar(ir, intSort, "x");
    ExprId i   = addVar(ir, intSort, "i");
    ExprId y   = addVar(ir, intSort, "y");   // only ever inside (> y 5)
    ExprId arr = addVar(ir, arrSort, "a");
    ExprId c5  = addConstInt(ir, intSort, 5);

    ExprId sel = addNode(ir, Kind::Select, intSort, {arr, i});       // index i is cared
    ExprId fx  = addNode(ir, Kind::UFApply, intSort, {x}, "f");      // arg x is cared
    ExprId eq  = addNode(ir, Kind::Eq, boolSort, {sel, fx});
    ExprId gt  = addNode(ir, Kind::Gt, boolSort, {y, c5});           // y is inert

    ir.addAssertion(eq);
    ir.addAssertion(gt);

    SharedTermRegistry reg;
    reg.setCoreIr(&ir);
    SharedTermId stX = reg.getOrCreate(x, intSort, "x", false);
    SharedTermId stI = reg.getOrCreate(i, intSort, "i", false);
    SharedTermId stY = reg.getOrCreate(y, intSort, "y", false);

    CareGraph cg;

    // Not built yet => conservative: every term is cared (identical to flag OFF).
    CHECK(cg.cares(stX));
    CHECK(cg.cares(stY));
    CHECK(cg.caresPair(stY, stY));

    cg.build(ir, reg);
    REQUIRE(cg.built());

    CHECK(cg.cares(stX));        // UFApply argument
    CHECK(cg.cares(stI));        // Select index
    CHECK_FALSE(cg.cares(stY));  // only operand of an arith relation (> y 5)

    // Pair pruning: keep if either endpoint is cared, skip only if both inert.
    CHECK(cg.caresPair(stX, stY));
    CHECK(cg.caresPair(stI, stY));
    CHECK_FALSE(cg.caresPair(stY, stY));
}

TEST_CASE("CareGraph: Eq/Distinct operands and internal bridge vars are cared") {
    CoreIr ir;
    const SortId intSort = 1, boolSort = 3;

    ExprId p = addVar(ir, intSort, "p");
    ExprId q = addVar(ir, intSort, "q");
    ExprId r = addVar(ir, intSort, "r");   // unused in any atom -> inert
    ExprId eqpq = addNode(ir, Kind::Eq, boolSort, {p, q});
    ir.addAssertion(eqpq);

    SharedTermRegistry reg;
    reg.setCoreIr(&ir);
    SharedTermId stP = reg.getOrCreate(p, intSort, "p", false);
    SharedTermId stQ = reg.getOrCreate(q, intSort, "q", false);
    SharedTermId stR = reg.getOrCreate(r, intSort, "r", false);
    // An internal (Purifier-style) bridge variable is always cared.
    ExprId bridge = addVar(ir, intSort, "bridge_0");
    SharedTermId stBridge = reg.getOrCreate(bridge, intSort, "bridge_0", true);

    CareGraph cg;
    cg.build(ir, reg);

    CHECK(cg.cares(stP));         // Eq operand
    CHECK(cg.cares(stQ));         // Eq operand
    CHECK_FALSE(cg.cares(stR));   // never appears in an inference-bearing node
    CHECK(cg.cares(stBridge));    // internal bridge var, always cared
}
