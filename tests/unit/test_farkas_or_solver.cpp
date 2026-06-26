// End-to-end P0→P1→P2a integration test for FarkasOrSolver.
//
// Build a CoreIr fragment that mirrors the Stroeder p21258 structure:
//   bounded globals: x ∈ [-1, 1], y ∈ [-1, 1]   (tightened from [-4,4] for test)
//   one Or block with 2 branches:
//     branch 0: λ_0, λ_1 ≥ 0
//                Eq:  -4·λ_0 + x·λ_1 = 0
//                Eq:   5·λ_0 + y·λ_1 = 0
//                Ineq: λ_0 + CT·λ_1 - 1 > 0
//     branch 1: same shape, swapped lambdas (irrelevant for SAT search)
//
// Expected: solveCsp finds B = (0, 0), choice 0 → ray (0, 1), CT ≥ 2.

#include "expr/ir.h"
#include "theory/arith/logics/nia/farkas/FarkasOrDetector.h"
#include "theory/arith/logics/nia/farkas/FarkasOrSolver.h"
#include "theory/arith/logics/nia/farkas/FarkasOrTypes.h"

#include <doctest/doctest.h>

#include <string>
#include <vector>

using namespace xolver;
using namespace xolver::farkas;

namespace {

struct IrB {
    CoreIr ir;
    SortId intSort;
    SortId realSort;
    IrB() {
        intSort = ir.allocateSortId();
        realSort = ir.allocateSortId();
        ir.setIntSortId(intSort);
        ir.setRealSortId(realSort);
    }
    ExprId v(std::string name, SortId s) {
        CoreExpr e; e.kind = Kind::Variable; e.sort = s;
        e.payload = Payload(std::move(name));
        return ir.add(std::move(e));
    }
    ExprId c(int64_t n) {
        CoreExpr e; e.kind = Kind::ConstReal; e.sort = realSort;
        e.payload = Payload(std::to_string(n));
        return ir.add(std::move(e));
    }
    ExprId mk(Kind k, std::vector<ExprId> ch) {
        CoreExpr e; e.kind = k; e.sort = realSort;
        for (auto x : ch) e.children.push_back(x);
        return ir.add(std::move(e));
    }
};

} // namespace

TEST_CASE("FarkasOrSolver: end-to-end Stroeder-shape 1-block 2-branch") {
    IrB b;

    // Bounded globals: x, y in [-1, 1].
    ExprId x  = b.v("x", b.intSort);
    ExprId y  = b.v("y", b.intSort);
    ExprId CT = b.v("CT", b.intSort);

    // Bound assertion: (and (<= -1 x) (<= x 1) (<= -1 y) (<= y 1))
    ExprId negOne  = b.mk(Kind::Neg, {b.c(1)});
    ExprId b1 = b.mk(Kind::Leq, {negOne, x});
    ExprId b2 = b.mk(Kind::Leq, {x, b.c(1)});
    ExprId b3 = b.mk(Kind::Leq, {negOne, y});
    ExprId b4 = b.mk(Kind::Leq, {y, b.c(1)});
    ExprId andBounds = b.mk(Kind::And, {b1, b2, b3, b4});
    b.ir.addAssertion(andBounds);

    // Branch 0: λ_0 = lam_a_0, λ_1 = lam_a_1.
    ExprId la0 = b.v("lam_a_0", b.intSort);
    ExprId la1 = b.v("lam_a_1", b.intSort);
    ExprId zero = b.c(0);
    // (>= λ_0 0) and (>= λ_1 0) — encoded as Leq(0, λ) per frontend form.
    ExprId nonneg_la0 = b.mk(Kind::Leq, {zero, la0});
    ExprId nonneg_la1 = b.mk(Kind::Leq, {zero, la1});
    // Eq: -4·λ_0 + x·λ_1 = 0
    ExprId mulA = b.mk(Kind::Mul, {b.mk(Kind::Neg, {b.c(4)}), la0});
    ExprId mulB = b.mk(Kind::Mul, {x, la1});
    ExprId eqA = b.mk(Kind::Eq, {b.mk(Kind::Add, {mulA, mulB}), zero});
    // Eq: 5·λ_0 + y·λ_1 = 0
    ExprId mulC = b.mk(Kind::Mul, {b.c(5), la0});
    ExprId mulD = b.mk(Kind::Mul, {y, la1});
    ExprId eqB = b.mk(Kind::Eq, {b.mk(Kind::Add, {mulC, mulD}), zero});
    // Ineq: (< 0 (+ λ_0 (* CT λ_1) -1))   (Stroeder frontend form)
    ExprId mulE = b.mk(Kind::Mul, {CT, la1});
    ExprId nNeg1 = b.mk(Kind::Neg, {b.c(1)});
    ExprId ineq = b.mk(Kind::Lt, {zero, b.mk(Kind::Add, {la0, mulE, nNeg1})});
    ExprId branch0 = b.mk(Kind::And,
                          {nonneg_la0, nonneg_la1, eqA, eqB, ineq});

    // Branch 1 (same shape but using different lambdas — same CT/x/y).
    // For the SAT test it doesn't need to be distinct; we just need TWO
    // branches so the propagator has a choice domain of size 2.
    ExprId lb0 = b.v("lam_b_0", b.intSort);
    ExprId lb1 = b.v("lam_b_1", b.intSort);
    ExprId nonneg_lb0 = b.mk(Kind::Leq, {zero, lb0});
    ExprId nonneg_lb1 = b.mk(Kind::Leq, {zero, lb1});
    ExprId mulA2 = b.mk(Kind::Mul, {b.mk(Kind::Neg, {b.c(4)}), lb0});
    ExprId mulB2 = b.mk(Kind::Mul, {x, lb1});
    ExprId eqA2 = b.mk(Kind::Eq, {b.mk(Kind::Add, {mulA2, mulB2}), zero});
    ExprId mulC2 = b.mk(Kind::Mul, {b.c(5), lb0});
    ExprId mulD2 = b.mk(Kind::Mul, {y, lb1});
    ExprId eqB2 = b.mk(Kind::Eq, {b.mk(Kind::Add, {mulC2, mulD2}), zero});
    ExprId mulE2 = b.mk(Kind::Mul, {CT, lb1});
    ExprId ineq2 = b.mk(Kind::Lt, {zero, b.mk(Kind::Add, {lb0, mulE2, nNeg1})});
    ExprId branch1 = b.mk(Kind::And,
                          {nonneg_lb0, nonneg_lb1, eqA2, eqB2, ineq2});

    // Or block.
    ExprId orBlock = b.mk(Kind::Or, {branch0, branch1});
    b.ir.addAssertion(orBlock);

    // Detect.
    FarkasOrDetector det(b.ir);
    auto profile = det.detect();
    REQUIRE(profile.blocks.size() == 1);
    REQUIRE(profile.blocks[0].branches.size() == 2);
    REQUIRE(profile.boundedGlobals.count("x"));
    REQUIRE(profile.boundedGlobals.count("y"));
    REQUIRE(profile.unboundedCT.count("CT"));

    // P2a end-to-end.
    FarkasOrSolver solver(b.ir);
    auto table = solver.buildTable(profile);
    CHECK(table.feasibleTotal > 0);

    auto assignment = solver.solveCsp(table, profile);
    REQUIRE(assignment.has_value());

    // Expected: x = 0, y = 0 in the assignment (other (x,y) with feasible
    // branches may also work but the propagator picks first-match).
    CHECK(assignment->B["x"] == 0);
    CHECK(assignment->B["y"] == 0);
    // Some branch chosen; ray's λ_1 should be 1 (the non-zero entry).
    REQUIRE(assignment->choice.count(0));
    REQUIRE(assignment->rayPerBlock.count(0));
    const auto& ray = assignment->rayPerBlock[0];
    REQUIRE(ray.size() == 2);
    CHECK(ray[0] == 0);
    CHECK(ray[1] == 1);
    // CT interval should be [2, +∞).
    REQUIRE(assignment->ctInterval.count("CT"));
    CHECK(assignment->ctFinite["CT"].first == true);    // ctLo finite
    CHECK(assignment->ctInterval["CT"].first == mpq_class(2));
}
