// Tests for UnconstrainedElim (drop relational atoms over single-occurrence
// variables; reconstruct the variable to a witness). Soundness end-to-end is
// covered by the Solver regression OFF+ON; here we test the pass mechanics +
// witness reconstruction.
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/UnconstrainedElim.h"
#include "frontend/preprocess/ModelConverter.h"
#include "util/RealValue.h"
#include <functional>

using namespace xolver;

namespace {
void setupSorts(CoreIr& ir, SortId& b, SortId& i, SortId& r) {
    b = ir.allocateSortId(); ir.registerSort(b, SortKind::Bool); ir.setBoolSortId(b);
    i = ir.allocateSortId(); ir.registerSort(i, SortKind::Int);  ir.setIntSortId(i);
    r = ir.allocateSortId(); ir.registerSort(r, SortKind::Real); ir.setRealSortId(r);
}
ExprId var(CoreIr& ir, SortId s, const char* n) { return ir.add(CoreExpr{Kind::Variable, s, {}, Payload(std::string(n))}); }
ExprId cint(CoreIr& ir, SortId s, int64_t v) { return ir.add(CoreExpr{Kind::ConstInt, s, {}, Payload(v)}); }
ExprId bin(CoreIr& ir, Kind k, SortId s, ExprId a, ExprId b) { return ir.add(CoreExpr{k, s, {a, b}, {}}); }
bool varInAssertions(const CoreIr& ir, const std::string& n) {
    std::function<bool(ExprId)> walk = [&](ExprId e) {
        const auto& nd = ir.get(e);
        if (nd.kind == Kind::Variable)
            if (auto* nm = std::get_if<std::string>(&nd.payload.value)) return *nm == n;
        for (ExprId c : nd.children) if (walk(c)) return true;
        return false;
    };
    for (ExprId a : ir.assertions()) if (walk(a)) return true;
    return false;
}
} // namespace

TEST_CASE("UnconstrainedElim: drops (>= x 5) when x occurs once, witness reconstructs >= 5") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x"), y = var(ir, i, "y");
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 5)));   // x >= 5  (x occurs only here)
    // y occurs TWICE -> constrained, must be KEPT (control).
    ir.addAssertion(bin(ir, Kind::Leq, b, y, cint(ir, i, 3)));   // y <= 3
    ir.addAssertion(bin(ir, Kind::Geq, b, y, cint(ir, i, 0)));   // y >= 0

    ModelConverter mc;
    UnconstrainedElim unc(ir, mc);
    REQUIRE(unc.run());
    unc.commit();
    CHECK(unc.eliminatedCount() == 1);
    CHECK(mc.size() == 1);
    CHECK_FALSE(varInAssertions(ir, "x"));   // dropped (single occurrence)
    CHECK(varInAssertions(ir, "y"));         // kept (two occurrences)

    // Witness: x >= 5 -> reconstruct to 5.
    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    REQUIRE(numAsg.count("x") == 1);
    CHECK(numAsg["x"].asRational() >= 5);
}

TEST_CASE("UnconstrainedElim: does NOT drop when the variable occurs more than once") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Geq, b, x, cint(ir, i, 5)));    // x >= 5
    ir.addAssertion(bin(ir, Kind::Leq, b, x, cint(ir, i, 10)));   // x <= 10  -> x occurs twice
    ModelConverter mc;
    UnconstrainedElim unc(ir, mc);
    CHECK_FALSE(unc.run());
    CHECK(mc.size() == 0);
}

TEST_CASE("UnconstrainedElim: strict < witness lands strictly below the bound") {
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Lt, b, x, cint(ir, i, 7)));   // x < 7, x only here
    ModelConverter mc;
    UnconstrainedElim unc(ir, mc);
    REQUIRE(unc.run());
    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    CHECK(numAsg["x"].asRational() < 7);
}

TEST_CASE("UnconstrainedElim: eliminates an unconstrained-var equality (x appears only in x=5)") {
    // be12735 extended UnconstrainedElim to Kind::Eq for the UNCONSTRAINED case:
    // x occurs exactly once (occ==1), here only in (= x 5), so x is determined by
    // that single equality and nothing else constrains it. Eliminating it (x -> 5)
    // is sound — reconstruct gives x = 5. (Previously UnconstrainedElim left all
    // equalities to solve-eqs; it now also claims the occ==1 equality case.)
    CoreIr ir; SortId b, i, r; setupSorts(ir, b, i, r);
    ExprId x = var(ir, i, "x");
    ir.addAssertion(bin(ir, Kind::Eq, b, x, cint(ir, i, 5)));
    ModelConverter mc;
    UnconstrainedElim unc(ir, mc);
    REQUIRE(unc.run());
    CHECK(mc.size() == 1);
    std::unordered_map<std::string, RealValue> numAsg;
    std::unordered_map<std::string, std::string> strAsg;
    REQUIRE(mc.reconstruct(numAsg, strAsg, ir));
    CHECK(numAsg["x"] == RealValue::fromInt(5));
}
