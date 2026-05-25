// Bit-blast module: BitVec readback + encoder ops + GA sorting + solver modes.
#include <doctest/doctest.h>
#include <gmpxx.h>
#include "sat/SatSolver.h"
#include "theory/arith/bit_blast/BitVec.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"

using namespace nlcolver;
using namespace nlcolver::bitblast;

TEST_CASE("BitVec: litValue reads polarity") {
    auto sat = createSatSolver();
    SatVar v = sat->newVar();
    sat->addClause({SatLit::positive(v)});   // force v = true
    REQUIRE(static_cast<int>(sat->solve()) ==
            static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(litValue(*sat, SatLit::positive(v)) == true);
    CHECK(litValue(*sat, SatLit::negative(v)) == false);
}

TEST_CASE("BitVec: readBitVec reconstructs two's-complement value") {
    auto sat = createSatSolver();
    // Build a 4-bit pattern for -3 = 1101 (LSB first: 1,0,1,1)
    auto force = [&](bool b) {
        SatVar v = sat->newVar();
        sat->addClause({b ? SatLit::positive(v) : SatLit::negative(v)});
        return SatLit::positive(v);
    };
    BitVec bv;
    bv.bits = { force(true), force(false), force(true), force(true) }; // -3
    REQUIRE(static_cast<int>(sat->solve()) ==
            static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, bv) == mpz_class(-3));
}

TEST_CASE("Encoder: andGate truth table") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    auto mk = [&](bool b){ SatVar v=sat->newVar();
        sat->addClause({b?SatLit::positive(v):SatLit::negative(v)}); return SatLit::positive(v); };
    SatLit c = enc.andGate(mk(true), mk(false));
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(litValue(*sat, c) == false);
}

TEST_CASE("Encoder: mkConst roundtrips through readBitVec") {
    for (long val : {0L, 1L, -1L, 7L, -8L, 42L, -42L}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec bv = enc.mkConst(mpz_class(val));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, bv) == mpz_class(val));
    }
}

TEST_CASE("Encoder: add of two constants") {
    for (auto pr : std::vector<std::pair<long,long>>{{3,4},{-3,4},{-5,-9},{0,0},{7,-8}}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec r = enc.add(enc.mkConst(mpz_class(pr.first)), enc.mkConst(mpz_class(pr.second)));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, r) == mpz_class(pr.first + pr.second));
    }
}

TEST_CASE("Encoder: sub and a free variable solve to a target") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(6);                 // signed 6-bit
    BitVec d = enc.sub(x, enc.mkConst(mpz_class(10)));   // x - 10
    enc.assertLit(enc.isZero(d));            // force x - 10 == 0
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, x) == mpz_class(10));
}

TEST_CASE("Encoder: mul of two constants (signed)") {
    for (auto pr : std::vector<std::pair<long,long>>{{3,4},{-3,4},{-5,-6},{0,9},{7,-8}}) {
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec r = enc.mul(enc.mkConst(mpz_class(pr.first)), enc.mkConst(mpz_class(pr.second)));
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, r) == mpz_class(pr.first) * mpz_class(pr.second));
    }
}

TEST_CASE("Encoder: powConst x^3 with x forced to -2") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.eq(x, enc.mkConst(mpz_class(-2))));
    BitVec c = enc.powConst(x, 3);                 // x^3
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, c) == mpz_class(-8));
}

TEST_CASE("Encoder: relZero Leq forces value <= 0") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.relZero(x, Relation::Leq));     // x <= 0
    enc.assertLit(enc.relZero(enc.add(x, enc.mkConst(mpz_class(3))), Relation::Geq)); // x+3 >= 0
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    mpz_class xv = readBitVec(*sat, x);
    CHECK(xv <= 0);
    CHECK(xv >= -3);
}

TEST_CASE("Encoder: relZero Geq + Leq pins value to 0 (Eq)") {
    auto sat = createSatSolver();
    BitBlastEncoder enc(*sat);
    BitVec x = enc.mkVar(5);
    enc.assertLit(enc.relZero(x, Relation::Eq));
    REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
    CHECK(readBitVec(*sat, x) == 0);
}

#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "theory/arith/poly/PolynomialKernel.h"

TEST_CASE("PolyBitBlaster: encode 2*x*y + 3 == 0 with x=3,y forced") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    // poly = 2*x*y + 3
    PolyId xy = kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy));
    PolyId poly = kernel->add(kernel->mul(kernel->mkConst(2), xy), kernel->mkConst(3));

    auto sat = createSatSolver();
    bitblast::BitBlastEncoder enc(*sat);
    std::unordered_map<std::string, bitblast::BitVec> vars;
    vars["x"] = enc.mkVar(6);
    vars["y"] = enc.mkVar(6);
    bitblast::PolyBitBlaster blaster(enc, *kernel, vars);
    // Force x = 3, then assert 2*x*y + 3 == 0  =>  6y + 3 == 0  => no integer y
    enc.assertLit(enc.eq(vars["x"], enc.mkConst(mpz_class(3))));
    blaster.assertConstraint({poly, Relation::Eq, SatLit{}});
    CHECK(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Unsat));
}

TEST_CASE("PolyBitBlaster: Greedy-Addition narrows max intermediate width") {
    auto kernel = createPolynomialKernel();
    // Four equal-width 3-bit-ish leaves a+b+c+d. GA folds (a+b)+(c+d) => width 5,
    // unsorted left-fold ((a+b)+c)+d => width 6. We check the GA folded width.
    std::vector<std::string> names{"a","b","c","d"};
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder enc(*sat);
    std::unordered_map<std::string, bitblast::BitVec> vars;
    PolyId sum = kernel->mkConst(0);
    for (auto& n : names) {
        VarId v = kernel->getOrCreateVar(n);
        vars[n] = enc.mkVar(3);
        sum = kernel->add(sum, kernel->mkVar(v));
    }
    bitblast::PolyBitBlaster blaster(enc, *kernel, vars);
    unsigned w = blaster.encodePolyWidth(sum);   // test-only accessor
    CHECK(w <= 5u);   // balanced GA tree, not the 6 of a linear chain
}

#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "theory/arith/nia/core/DomainStore.h"

TEST_CASE("SpaceEstimator: bitsToCover") {
    using bitblast::SpaceEstimator;
    CHECK(SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(0)) == 1u);   // {0}
    CHECK(SpaceEstimator::bitsToCover(mpz_class(-1), mpz_class(0)) == 1u);  // {-1,0}
    CHECK(SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(7)) == 4u);   // 0..7 needs sign+3
    CHECK(SpaceEstimator::bitsToCover(mpz_class(-8), mpz_class(7)) == 4u);
}

TEST_CASE("SpaceEstimator: boxIsComplete only when all vars hard-bounded") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId p = kernel->add(kernel->mkVar(vx), kernel->mkVar(vy));   // x + y
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{}}};

    bitblast::SpaceEstimator est(*kernel);

    DomainStore d1;     // only x bounded
    d1.addLowerBound("x", mpz_class(-4), SatLit{1, true});
    d1.addUpperBound("x", mpz_class(4),  SatLit{2, true});
    auto plan1 = est.estimate(cs, d1);
    CHECK(plan1.boxIsComplete == false);
    CHECK(plan1.width.count("x") == 1);
    CHECK(plan1.width.count("y") == 1);

    DomainStore d2;     // both bounded
    d2.addLowerBound("x", mpz_class(-4), SatLit{1, true});
    d2.addUpperBound("x", mpz_class(4),  SatLit{2, true});
    d2.addLowerBound("y", mpz_class(0),  SatLit{3, true});
    d2.addUpperBound("y", mpz_class(15), SatLit{4, true});
    auto plan2 = est.estimate(cs, d2);
    CHECK(plan2.boxIsComplete == true);
    CHECK(plan2.width.at("y") == SpaceEstimator::bitsToCover(mpz_class(0), mpz_class(15)));
}

#include "theory/arith/bit_blast/BitBlastSolver.h"
#include "theory/arith/nia/search/IntegerModelValidator.h"

// SOUNDNESS REGRESSION (reviewer's counterexample): bounds live ONLY in
// DomainStore, NOT in cs. The solver must still confine the search to the box
// (explicit bound encoding) and reject out-of-box models (modelInDomains).
// A naive "encode cs + validate cs" would wrongly accept x=-1,y=-6.
TEST_CASE("BitBlastSolver: SAT respects DomainStore bounds even when cs omits them") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId prod = kernel->sub(kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy)), kernel->mkConst(6));
    std::vector<NormalizedNiaConstraint> cs{{prod, Relation::Eq, SatLit{10, true}}}; // ONLY x*y-6==0
    DomainStore d;   // bounds ONLY here — never added to cs
    for (auto n : {"x","y"}) { d.addLowerBound(n, mpz_class(0), SatLit{11,true});
                               d.addUpperBound(n, mpz_class(6), SatLit{12,true}); }
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    REQUIRE(r.status == bitblast::BitBlastResult::Status::Sat);
    CHECK(r.model.at("x") * r.model.at("y") == 6);
    CHECK(r.model.at("x") >= 0); CHECK(r.model.at("x") <= 6);   // box enforced, not just x*y=6
    CHECK(r.model.at("y") >= 0); CHECK(r.model.at("y") <= 6);   // would FAIL if x=-1,y=-6 accepted
}

TEST_CASE("BitBlastSolver: complete box UNSAT carries nonlinear AND bound reasons") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    // x*x = 2 has no integer root; x in [-3,3] (DomainStore) is the whole feasible box.
    PolyId sq = kernel->sub(kernel->pow(kernel->mkVar(vx), 2), kernel->mkConst(2));
    std::vector<NormalizedNiaConstraint> cs{{sq, Relation::Eq, SatLit{20, true}}}; // ONLY x*x-2==0
    DomainStore d;
    d.addLowerBound("x", mpz_class(-3), SatLit{21,true});
    d.addUpperBound("x", mpz_class(3),  SatLit{22,true});
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    REQUIRE(r.status == bitblast::BitBlastResult::Status::UnsatComplete);
    REQUIRE(r.conflict.has_value());
    bool hasNonlinear = false, hasLower = false, hasUpper = false;
    for (const auto& l : r.conflict->clause) {
        if (l.var == 20) hasNonlinear = true;
        if (l.var == 21) hasLower = true;
        if (l.var == 22) hasUpper = true;
    }
    CHECK(hasNonlinear); CHECK(hasLower); CHECK(hasUpper);
}

TEST_CASE("BitBlastSolver: unbounded UNSAT returns Unknown, never UNSAT") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId p = kernel->sub(kernel->pow(kernel->mkVar(vx), 2), kernel->mkConst(2));
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{30, true}}};
    DomainStore d;   // x unbounded => boxIsComplete is false
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    solver.setMaxIterations(2);   // keep the test fast; verdict is mode-invariant
    auto r = solver.solve(cs, d, validator);
    CHECK(r.status == bitblast::BitBlastResult::Status::Unknown);
}

// Point 1/3: a bound that was ENCODED but lacks a usable reason must force
// Unknown — never a partial (unsound) conflict.
TEST_CASE("BitBlastSolver: missing reason on an encoded bound => Unknown, not a bad conflict") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    PolyId p = kernel->sub(kernel->mkVar(vx), kernel->mkConst(5));      // x - 5
    std::vector<NormalizedNiaConstraint> cs{{p, Relation::Eq, SatLit{40, true}}}; // x == 5
    DomainStore d;
    d.addLowerBound("x", mpz_class(0), SatLit{41, true});
    d.addUpperBound("x", mpz_class(3), SatLit{});   // upper bound has NO usable reason (var 0)
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    CHECK(r.status == bitblast::BitBlastResult::Status::Unknown);
}

// Point 2: a variable that appears ONLY in DomainStore (not in cs) is still
// encoded; a contradictory domain-only var must be detected (no spurious SAT).
TEST_CASE("BitBlastSolver: domain-only variable inconsistency is detected") {
    auto kernel = createPolynomialKernel();
    VarId vx = kernel->getOrCreateVar("x");
    VarId vy = kernel->getOrCreateVar("y");
    PolyId prod = kernel->sub(kernel->mul(kernel->mkVar(vx), kernel->mkVar(vy)), kernel->mkConst(6));
    std::vector<NormalizedNiaConstraint> cs{{prod, Relation::Eq, SatLit{50, true}}}; // only x,y in cs
    DomainStore d;
    for (auto n : {"x","y"}) { d.addLowerBound(n, mpz_class(0), SatLit{51,true});
                               d.addUpperBound(n, mpz_class(6), SatLit{52,true}); }
    // z appears ONLY in domains, with an empty interval [5,3] => whole state UNSAT.
    d.addLowerBound("z", mpz_class(5), SatLit{53,true});
    d.addUpperBound("z", mpz_class(3), SatLit{54,true});
    IntegerModelValidator validator(*kernel);
    bitblast::BitBlastSolver solver(*kernel);
    auto r = solver.solve(cs, d, validator);
    CHECK(r.status != bitblast::BitBlastResult::Status::Sat);
}

#include "theory/arith/nia/NiaSolver.h"
#include <algorithm>

// Real registration check: the bit-blast stage must appear by name in the NIA
// reasoner pipeline, immediately AFTER "nia.bounded" and BEFORE
// "nia.local-search". A construct-and-check-id() test would pass even without
// the stage, so we introspect the pipeline order instead.
TEST_CASE("NiaSolver: bit-blast stage registered between bounded and local-search") {
    auto kernel = createPolynomialKernel();
    NiaSolver solver(std::move(kernel));
    auto names = solver.reasonerNames();
    auto bb = std::find(names.begin(), names.end(), "nia.bit-blast");
    auto bd = std::find(names.begin(), names.end(), "nia.bounded");
    auto ls = std::find(names.begin(), names.end(), "nia.local-search");
    REQUIRE(bb != names.end());
    REQUIRE(bd != names.end());
    REQUIRE(ls != names.end());
    CHECK(bd < bb);    // after bounded
    CHECK(bb < ls);    // before local-search
}
