// H2 MonomialSharingPass — unit tests pinning the soundness invariant
// master flagged: shared Mul nodes are NAMED via fresh m_<n> vars + ONE
// definitional assertion m_<n> = (* x y), never eliminated.

#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/MonomialSharingPass.h"

using namespace xolver;

namespace {

struct IrFixture {
    CoreIr ir;
    SortId boolSort = 1;
    SortId intSort = 2;
    SortId realSort = 3;

    ExprId mkVar(const std::string& name, SortId sort) {
        CoreExpr e;
        e.kind = Kind::Variable;
        e.sort = sort;
        e.payload = Payload(name);
        return ir.add(std::move(e));
    }
    ExprId mkConstInt(int64_t v) {
        CoreExpr e;
        e.kind = Kind::ConstInt;
        e.sort = intSort;
        e.payload = Payload(v);
        return ir.add(std::move(e));
    }
    ExprId mkMul(ExprId a, ExprId b) {
        CoreExpr e;
        e.kind = Kind::Mul;
        e.sort = intSort;
        e.children.push_back(a);
        e.children.push_back(b);
        return ir.add(std::move(e));
    }
    ExprId mkAdd(ExprId a, ExprId b) {
        CoreExpr e;
        e.kind = Kind::Add;
        e.sort = intSort;
        e.children.push_back(a);
        e.children.push_back(b);
        return ir.add(std::move(e));
    }
    ExprId mkEq(ExprId a, ExprId b) {
        CoreExpr e;
        e.kind = Kind::Eq;
        e.sort = boolSort;
        e.children.push_back(a);
        e.children.push_back(b);
        return ir.add(std::move(e));
    }
    ExprId mkGeq(ExprId a, ExprId b) {
        CoreExpr e;
        e.kind = Kind::Geq;
        e.sort = boolSort;
        e.children.push_back(a);
        e.children.push_back(b);
        return ir.add(std::move(e));
    }
};

}  // namespace

TEST_CASE("MonomialSharingPass: no sharing when monomial appears in 1 assertion") {
    IrFixture f;
    ExprId x = f.mkVar("x", f.intSort);
    ExprId y = f.mkVar("y", f.intSort);
    ExprId xy = f.mkMul(x, y);
    ExprId zero = f.mkConstInt(0);
    // Single assertion: x*y >= 0.
    ExprId a1 = f.mkGeq(xy, zero);
    f.ir.addAssertion(a1, 0);

    MonomialSharingPass pass(f.ir, f.intSort, f.realSort, f.boolSort);
    size_t selected = pass.run();
    CHECK(selected == 0);  // refCount = 1 < threshold 2
    pass.commit();
    // Assertion list unchanged.
    CHECK(f.ir.getScopedAssertions().size() == 1);
}

TEST_CASE("MonomialSharingPass: shares Mul appearing in 2 distinct assertions") {
    IrFixture f;
    ExprId x = f.mkVar("x", f.intSort);
    ExprId y = f.mkVar("y", f.intSort);
    ExprId xy = f.mkMul(x, y);
    ExprId zero = f.mkConstInt(0);
    ExprId one = f.mkConstInt(1);
    // Assertion 1: x*y >= 0
    f.ir.addAssertion(f.mkGeq(xy, zero), 0);
    // Assertion 2: x*y >= 1
    f.ir.addAssertion(f.mkGeq(xy, one), 0);

    MonomialSharingPass pass(f.ir, f.intSort, f.realSort, f.boolSort);
    size_t selected = pass.run();
    CHECK(selected == 1);
    pass.commit();

    const auto& asserts = f.ir.getScopedAssertions();
    // 2 rewritten assertions + 1 definitional (= m_<0> (* x y)) = 3 total.
    CHECK(asserts.size() == 3);

    // Find the definitional assertion: an Eq whose RHS is the original Mul.
    bool foundDef = false;
    ExprId mvarId = NullExpr;
    for (const auto& [lvl, a] : asserts) {
        const auto& n = f.ir.get(a);
        if (n.kind == Kind::Eq && n.children.size() == 2) {
            ExprId lhs = n.children[0];
            ExprId rhs = n.children[1];
            const auto& rn = f.ir.get(rhs);
            if (rn.kind == Kind::Mul) {
                foundDef = true;
                CHECK(lvl == 0);  // base scope
                mvarId = lhs;
                // RHS is the original Mul ExprId.
                CHECK(rhs == xy);
                CHECK(f.ir.get(lhs).kind == Kind::Variable);
            }
        }
    }
    CHECK(foundDef);

    // Both original assertions should now reference the fresh m_var, not xy.
    int rewrittenCount = 0;
    for (const auto& [lvl, a] : asserts) {
        const auto& n = f.ir.get(a);
        if (n.kind != Kind::Geq) continue;
        ++rewrittenCount;
        // The LHS of the Geq must now be the fresh m_var.
        CHECK(n.children[0] == mvarId);
    }
    CHECK(rewrittenCount == 2);
}

TEST_CASE("MonomialSharingPass: nested Mul inside arithmetic gets shared") {
    IrFixture f;
    ExprId x = f.mkVar("x", f.intSort);
    ExprId y = f.mkVar("y", f.intSort);
    ExprId xy = f.mkMul(x, y);
    ExprId k = f.mkConstInt(5);
    ExprId xyPlusK = f.mkAdd(xy, k);
    ExprId zero = f.mkConstInt(0);
    // Assertion 1: x*y + 5 >= 0
    f.ir.addAssertion(f.mkGeq(xyPlusK, zero), 0);
    // Assertion 2: x*y + 5 = 0  (uses same xyPlusK ExprId by hash-cons miss
    // since we don't have cons here, but the Mul x*y is shared via xy)
    ExprId xyPlusKEq = f.mkAdd(xy, k);
    f.ir.addAssertion(f.mkEq(xyPlusKEq, zero), 0);

    MonomialSharingPass pass(f.ir, f.intSort, f.realSort, f.boolSort);
    size_t selected = pass.run();
    CHECK(selected == 1);  // xy shared across both
    pass.commit();
    // 2 rewritten + 1 def = 3 assertions
    CHECK(f.ir.getScopedAssertions().size() == 3);
}

TEST_CASE("MonomialSharingPass: pure constant Mul not shareable") {
    IrFixture f;
    ExprId two = f.mkConstInt(2);
    ExprId three = f.mkConstInt(3);
    ExprId sixConst = f.mkMul(two, three);  // 2*3 — both constants
    ExprId zero = f.mkConstInt(0);
    f.ir.addAssertion(f.mkGeq(sixConst, zero), 0);
    f.ir.addAssertion(f.mkEq(sixConst, zero), 0);

    MonomialSharingPass pass(f.ir, f.intSort, f.realSort, f.boolSort);
    size_t selected = pass.run();
    CHECK(selected == 0);  // both factors const => not shareable
    pass.commit();
    CHECK(f.ir.getScopedAssertions().size() == 2);
}

TEST_CASE("MonomialSharingPass: shareable when one operand is a Variable, one is a Mul") {
    IrFixture f;
    ExprId x = f.mkVar("x", f.intSort);
    ExprId y = f.mkVar("y", f.intSort);
    ExprId z = f.mkVar("z", f.intSort);
    ExprId yz = f.mkMul(y, z);
    ExprId xyz = f.mkMul(x, yz);  // x * (y*z); both children non-const
    ExprId zero = f.mkConstInt(0);
    f.ir.addAssertion(f.mkGeq(xyz, zero), 0);
    f.ir.addAssertion(f.mkEq(xyz, zero), 0);

    MonomialSharingPass pass(f.ir, f.intSort, f.realSort, f.boolSort);
    size_t selected = pass.run();
    // BOTH x*y*z (the outer Mul) AND y*z (the inner Mul, reached in BOTH
    // assertions) are shareable. Either order, at least 1; current impl
    // captures both.
    CHECK(selected >= 1);
    pass.commit();
    // 2 rewritten + selected def assertions.
    CHECK(f.ir.getScopedAssertions().size() == 2 + selected);
}
