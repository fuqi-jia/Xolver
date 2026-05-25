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
