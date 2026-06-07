// Replay-correctness tests for ModelConverter (reconstruction of variables
// eliminated by solve-eqs). The reconstructed model must give eliminated vars
// the value of their defining term under the rest of the model.
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/ModelConverter.h"
#include "util/RealValue.h"

using namespace xolver;

namespace {
void setupSorts(CoreIr& ir, SortId& b, SortId& i, SortId& r) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
}
ExprId var(CoreIr& ir, SortId s, const char* n) {
    return ir.add(CoreExpr{Kind::Variable, s, {}, Payload(std::string(n))});
}
ExprId cint(CoreIr& ir, SortId s, int64_t v) {
    return ir.add(CoreExpr{Kind::ConstInt, s, {}, Payload(v)});
}
ExprId add(CoreIr& ir, SortId s, ExprId a, ExprId b) {
    return ir.add(CoreExpr{Kind::Add, s, {a, b}, {}});
}
} // namespace

TEST_CASE("ModelConverter: reconstructs x = y + 1 from the model of y") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId t = add(ir, i, var(ir, i, "y"), cint(ir, i, 1));   // y + 1

    ModelConverter mc;
    mc.registerElimination("x", i, t);

    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    numAsg["y"] = RealValue::fromInt(4);

    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    REQUIRE(numAsg.count("x") == 1);
    CHECK(numAsg["x"] == RealValue::fromInt(5));
    CHECK(strAsg["x"] == "5");   // string channel (modelMatchesOriginal/dumpModel)
}

TEST_CASE("ModelConverter: reverse-order replay resolves chained eliminations") {
    // Eliminated in order:  x = y + 1   (registered first),
    //                       y = z + 2   (registered second).
    // Over {z = 10}, reverse replay must give y = 12 then x = 13.
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId tx = add(ir, i, var(ir, i, "y"), cint(ir, i, 1));   // y + 1
    ExprId ty = add(ir, i, var(ir, i, "z"), cint(ir, i, 2));   // z + 2

    ModelConverter mc;
    mc.registerElimination("x", i, tx);
    mc.registerElimination("y", i, ty);

    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    numAsg["z"] = RealValue::fromInt(10);

    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    CHECK(numAsg["y"] == RealValue::fromInt(12));
    CHECK(numAsg["x"] == RealValue::fromInt(13));
}

TEST_CASE("ModelConverter: missing dependency leaves reconstruct() false") {
    // x = w + 1 but w is not in the model and not eliminated -> cannot rebuild.
    // STRICT Elim path (SolveEqs): a missing free var is a solver bug, so
    // reconstruct() must fail loudly rather than invent a value (a39f26c).
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId t = add(ir, i, var(ir, i, "w"), cint(ir, i, 1));

    ModelConverter mc;
    mc.registerElimination("x", i, t);

    std::unordered_map<std::string, RealValue> numAsg;  // empty
    std::unordered_map<std::string, std::string> strAsg;
    CHECK_FALSE(mc.reconstruct(numAsg, strAsg, ir));
}
