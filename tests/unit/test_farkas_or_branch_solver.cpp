// Unit tests for FarkasOrBranchSolver (P1). Build small NativeTerms fragments
// that mirror Stroeder-style Farkas branches; verify the solver produces
// the expected primitive non-negative ray + CT interval.

#include "ir/NativeTerms.h"
#include "search/nia/farkas/FarkasOrBranchSolver.h"
#include "search/nia/farkas/FarkasOrTypes.h"
#include "evidence/ArithModelValidator.h"

#include <doctest/doctest.h>

#include <string>
#include <unordered_map>
#include <vector>

using namespace xolver;
using namespace xolver::farkas;

namespace {

// Tiny NativeTerms builder for tests.
struct IrBuilder {
    NativeTerms ir;
    SortId intSort;
    SortId realSort;
    SortId boolSort;

    IrBuilder() {
        intSort = ir.allocateSortId();
        realSort = ir.allocateSortId();
        ir.registerSort(intSort, SortKind::Int);
        ir.registerSort(realSort, SortKind::Real);
        boolSort = ir.allocateSortId();
        ir.registerSort(boolSort, SortKind::Bool);
        ir.setIntSortId(intSort);
        ir.setRealSortId(realSort);
    }

    ExprId mkVar(std::string name, SortId s) {
        TermExpr e;
        e.kind = Kind::Variable;
        e.sort = s;
        e.payload = Payload(std::move(name));
        return ir.add(std::move(e));
    }
    ExprId mkConst(int64_t v) {
        TermExpr e;
        e.kind = Kind::ConstReal;        // mirror frontend's QF_NIA lift
        e.sort = realSort;
        e.payload = Payload(std::to_string(v));
        return ir.add(std::move(e));
    }
    ExprId mk(Kind k, std::vector<ExprId> ch) {
        TermExpr e;
        e.kind = k;
        e.sort = realSort;
        if (e.isAtom() || k == Kind::And || k == Kind::Or || k == Kind::Not) e.sort = boolSort;
        for (auto c : ch) e.children.push_back(c);
        return ir.add(std::move(e));
    }
};

} // namespace

TEST_CASE("FarkasOrBranchSolver: Stroeder-shape branch[0] under B=(0,0)") {
    // Branch[0] of Stroeder p21258 Or id=160:
    //   λ_0 = lam0n0, λ_1 = lam0n1
    //   Eq1: -4*lam0n0 + x*lam0n1 = 0     (x = Nl2main_x1)
    //   Eq2:  5*lam0n0 + y*lam0n1 = 0     (y = Nl2main_y1)
    //   Ineq: lam0n0 + CT*lam0n1 - 1 > 0  (CT = Nl2CT1)
    // Under B = {x:0, y:0}: lam0n0 = 0; ray = (0, 1) primitive; CT ≥ 2.

    IrBuilder b;
    ExprId lam0 = b.mkVar("lam0n0", b.intSort);
    ExprId lam1 = b.mkVar("lam0n1", b.intSort);
    ExprId X    = b.mkVar("Nl2main_x1", b.intSort);
    ExprId Y    = b.mkVar("Nl2main_y1", b.intSort);
    ExprId CT   = b.mkVar("Nl2CT1",     b.intSort);
    ExprId zero = b.mkConst(0);
    ExprId one  = b.mkConst(1);
    ExprId neg4 = b.mk(Kind::Neg, {b.mkConst(4)});
    ExprId five = b.mkConst(5);

    // Eq1: (= (+ (* -4 lam0n0) (* x lam0n1)) 0)
    ExprId mulA = b.mk(Kind::Mul, {neg4, lam0});
    ExprId mulB = b.mk(Kind::Mul, {X, lam1});
    ExprId addE1 = b.mk(Kind::Add, {mulA, mulB});
    ExprId eq1 = b.mk(Kind::Eq, {addE1, zero});

    // Eq2: (= (+ (* 5 lam0n0) (* y lam0n1)) 0)
    ExprId mulC = b.mk(Kind::Mul, {five, lam0});
    ExprId mulD = b.mk(Kind::Mul, {Y, lam1});
    ExprId addE2 = b.mk(Kind::Add, {mulC, mulD});
    ExprId eq2 = b.mk(Kind::Eq, {addE2, zero});

    // Ineq: (> (+ lam0n0 (* CT lam0n1) -1) 0) — modelled here as
    //   (< 0 (+ lam0n0 (* CT lam0n1) -1))     [Stroeder's frontend form]
    ExprId mulE = b.mk(Kind::Mul, {CT, lam1});
    ExprId negOne = b.mk(Kind::Neg, {one});
    ExprId addI = b.mk(Kind::Add, {lam0, mulE, negOne});
    ExprId ineq = b.mk(Kind::Lt, {zero, addI});

    // Lambda non-negativity (not needed to be added — solver doesn't see them).
    FarkasBranch branch;
    branch.originalAnd = NullExpr;     // unused in solver
    branch.lambdas = {"lam0n0", "lam0n1"};
    branch.equalities = {eq1, eq2};
    branch.inequalities = {ineq};

    std::unordered_map<std::string, mpz_class> B = {
        {"Nl2main_x1", mpz_class(0)},
        {"Nl2main_y1", mpz_class(0)},
    };
    std::vector<std::string> ctVars = {"Nl2CT1"};

    FarkasOrBranchSolver solver(b.ir);
    auto candidates = solver.solveBranch(branch, B, ctVars);

    REQUIRE(!candidates.empty());
    // We expect at least one candidate with ray = (0, 1).
    bool foundExpected = false;
    for (const auto& c : candidates) {
        if (c.lambdaRay.size() == 2 &&
            c.lambdaRay[0] == 0 && c.lambdaRay[1] == 1) {
            foundExpected = true;
            REQUIRE(c.ctBounds.size() == 1);
            const auto& bd = c.ctBounds[0];
            // After substituting ray = (0, 1), the inequality residual is:
            //   0 + CT*1 + (-1) >= 1  (Lt(0, x) → Gt(x, 0) → x ≥ 1 integer)
            // → CT - 1 ≥ 1  → CT ≥ 2.
            REQUIRE(bd.hasInterval);
            CHECK(bd.ctVar == "Nl2CT1");
            CHECK(bd.ctLoFinite);
            CHECK(bd.ctLo == mpq_class(2));
        }
    }
    CHECK(foundExpected);
}

TEST_CASE("FarkasOrBranchSolver: B-substitution makes equality trivial") {
    // Eq: (= (* x lam0) 0)  under B={x:0} → 0 = 0 (vacuously true).
    // The nullspace is all-1 vector; ray = (1) primitive.
    IrBuilder b;
    ExprId lam0 = b.mkVar("lam0", b.intSort);
    ExprId X    = b.mkVar("x",    b.intSort);
    ExprId zero = b.mkConst(0);
    ExprId mul  = b.mk(Kind::Mul, {X, lam0});
    ExprId eq   = b.mk(Kind::Eq, {mul, zero});

    FarkasBranch branch;
    branch.lambdas = {"lam0"};
    branch.equalities = {eq};

    std::unordered_map<std::string, mpz_class> B = {{"x", mpz_class(0)}};
    FarkasOrBranchSolver solver(b.ir);
    auto cands = solver.solveBranch(branch, B, {});
    REQUIRE(!cands.empty());
    CHECK(cands[0].lambdaRay.size() == 1);
    CHECK(cands[0].lambdaRay[0] == 1);
}

TEST_CASE("FarkasOrBranchSolver: non-homogeneous unique solution (P1 v2)") {
    // Eq: (= lam0 1)  under any B — particular solution lam0 = 1.
    // P1 v1 rejected this; P1 v2 returns ray = [1].
    IrBuilder b;
    ExprId lam0 = b.mkVar("lam0", b.intSort);
    ExprId one  = b.mkConst(1);
    ExprId eq   = b.mk(Kind::Eq, {lam0, one});

    FarkasBranch branch;
    branch.lambdas = {"lam0"};
    branch.equalities = {eq};

    FarkasOrBranchSolver solver(b.ir);
    auto cands = solver.solveBranch(branch, {}, {});
    REQUIRE(!cands.empty());
    bool found = false;
    for (const auto& c : cands) {
        if (c.lambdaRay.size() == 1 && c.lambdaRay[0] == 1) {
            found = true; break;
        }
    }
    CHECK(found);
}

TEST_CASE("FarkasOrBranchSolver: non-homogeneous parametric, B != 0 (P1 v2)") {
    // Eq1: -4*lam0 + x*lam1 = 4*y    (rewritten so the RHS is non-zero)
    // i.e. (= (- (+ (* -4 lam0) (* x lam1)) (* 4 y)) 0)
    // Under B = {x:4, y:1}:
    //   -4·lam0 + 4·lam1 - 4 = 0
    //   → lam1 = lam0 + 1
    //   particular lam0=0, lam1=1 — non-neg integer.
    IrBuilder b;
    ExprId lam0 = b.mkVar("lam0", b.intSort);
    ExprId lam1 = b.mkVar("lam1", b.intSort);
    ExprId X    = b.mkVar("x",    b.intSort);
    ExprId Y    = b.mkVar("y",    b.intSort);
    ExprId zero = b.mkConst(0);
    ExprId neg4 = b.mk(Kind::Neg, {b.mkConst(4)});
    ExprId four = b.mkConst(4);
    ExprId mulA = b.mk(Kind::Mul, {neg4, lam0});
    ExprId mulB = b.mk(Kind::Mul, {X, lam1});
    ExprId mul4y = b.mk(Kind::Mul, {four, Y});
    ExprId addLam = b.mk(Kind::Add, {mulA, mulB});
    ExprId sub = b.mk(Kind::Sub, {addLam, mul4y});
    ExprId eq = b.mk(Kind::Eq, {sub, zero});

    FarkasBranch branch;
    branch.lambdas = {"lam0", "lam1"};
    branch.equalities = {eq};

    std::unordered_map<std::string, mpz_class> B = {
        {"x", mpz_class(4)},
        {"y", mpz_class(1)},
    };
    FarkasOrBranchSolver solver(b.ir);
    auto cands = solver.solveBranch(branch, B, {});
    REQUIRE(!cands.empty());
    bool found = false;
    for (const auto& c : cands) {
        // Verify the candidate satisfies -4·ray[0] + 4·ray[1] = 4.
        if (c.lambdaRay.size() == 2) {
            mpz_class lhs = mpz_class(-4) * c.lambdaRay[0] + mpz_class(4) * c.lambdaRay[1];
            if (lhs == 4 && c.lambdaRay[0] >= 0 && c.lambdaRay[1] >= 0) {
                found = true;
                break;
            }
        }
    }
    CHECK(found);
}

TEST_CASE("FarkasOrBranchSolver: truly infeasible non-homogeneous (P1 v2)") {
    // Eq: (= (* 2 lam0) 1)  — 2·lam0 = 1 has no integer solution.
    IrBuilder b;
    ExprId lam0 = b.mkVar("lam0", b.intSort);
    ExprId two  = b.mkConst(2);
    ExprId one  = b.mkConst(1);
    ExprId mul  = b.mk(Kind::Mul, {two, lam0});
    ExprId eq   = b.mk(Kind::Eq, {mul, one});

    FarkasBranch branch;
    branch.lambdas = {"lam0"};
    branch.equalities = {eq};

    FarkasOrBranchSolver solver(b.ir);
    auto cands = solver.solveBranch(branch, {}, {});
    CHECK(cands.empty());
}

TEST_CASE("FarkasOrBranchSolver: exact ray scaling reaches strict integer boundaries") {
    for (int64_t lower : {int64_t(1), int64_t(7), int64_t(2147483649),
                          int64_t(1099511627776)}) {
        CAPTURE(lower);
        IrBuilder b;
        const auto p = b.mkVar("p", b.intSort), q = b.mkVar("q", b.intSort);
        const auto zero = b.mkConst(0);
        const auto equation = b.mk(Kind::Eq, {b.mk(Kind::Sub, {p, q}), zero});
        const auto strict = b.mk(Kind::Gt, {p, b.mkConst(lower)});
        const auto upper = b.mk(Kind::Leq, {p, b.mkConst(lower + 1)});
        FarkasBranch branch;
        branch.lambdas = {"p", "q"}; branch.equalities = {equation};
        branch.inequalities = {strict, upper};
        b.ir.addAssertion(b.mk(Kind::And, {equation, strict, upper}));
        const auto candidates = FarkasOrBranchSolver(b.ir).solveBranch(branch, {}, {});
        bool verified = false;
        for (const auto& candidate : candidates) {
            REQUIRE(candidate.lambdaRay.size() == 2);
            const ArithModelValidator::NumAssignment model{
                {"p", mpq_class(candidate.lambdaRay[0])},
                {"q", mpq_class(candidate.lambdaRay[1])}};
            const ArithModelValidator::BoolAssignment booleans;
            if (ArithModelValidator(b.ir, model, booleans).validate(b.ir.assertions())
                == ArithModelValidator::Verdict::Satisfied) verified = true;
        }
        CHECK(verified);
    }
}

TEST_CASE("FarkasOrBranchSolver: scaling respects upper bounds and nonzero equality RHS") {
    IrBuilder b;
    const auto p = b.mkVar("p", b.intSort), q = b.mkVar("q", b.intSort);
    const auto zero = b.mkConst(0);
    FarkasBranch branch;
    branch.lambdas = {"p", "q"};
    branch.equalities = {b.mk(Kind::Eq, {b.mk(Kind::Sub, {p, q}), zero})};
    branch.inequalities = {b.mk(Kind::Gt, {p, b.mkConst(3)}),
                           b.mk(Kind::Leq, {p, b.mkConst(3)})};
    CHECK(FarkasOrBranchSolver(b.ir).solveBranch(branch, {}, {}).empty());
    branch.equalities = {b.mk(Kind::Eq, {p, b.mkConst(1)})};
    branch.lambdas = {"p"};
    branch.inequalities = {b.mk(Kind::Gt, {p, b.mkConst(1)})};
    CHECK(FarkasOrBranchSolver(b.ir).solveBranch(branch, {}, {}).empty());
}

TEST_CASE("FarkasOrBranchSolver: cost intervals are rebuilt at the scaled ray") {
    IrBuilder b;
    const auto p = b.mkVar("p", b.intSort), q = b.mkVar("q", b.intSort);
    const auto cost = b.mkVar("cost", b.intSort), zero = b.mkConst(0);
    FarkasBranch branch;
    branch.lambdas = {"p", "q"};
    branch.equalities = {b.mk(Kind::Eq, {b.mk(Kind::Sub, {p, q}), zero})};
    branch.inequalities = {b.mk(Kind::Gt, {p, b.mkConst(3)}),
        b.mk(Kind::Lt, {b.mk(Kind::Mul, {p, cost}), b.mkConst(7)})};
    const auto candidates = FarkasOrBranchSolver(b.ir).solveBranch(branch, {}, {"cost"});
    REQUIRE_FALSE(candidates.empty());
    for (const auto& candidate : candidates) {
        REQUIRE(candidate.lambdaRay.size() == 2);
        CHECK(candidate.lambdaRay[0] == 4);
        REQUIRE(candidate.ctBounds.size() == 2);
        CHECK(candidate.ctBounds[1].ctHi == mpq_class(3, 2));
    }
}
