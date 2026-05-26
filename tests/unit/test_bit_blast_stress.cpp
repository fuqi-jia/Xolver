// Randomized property tests: the bit-blast encoder's arithmetic and comparison
// operations must match exact integer (GMP) arithmetic over forced-variable
// operands, across many random inputs and boundary widths.
#include <doctest/doctest.h>
#include <gmpxx.h>
#include <random>
#include <vector>
#include "sat/SatSolver.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"

using namespace zolver;
using namespace zolver::bitblast;

// Allocate a fresh variable bit-vector of the given width and pin it to `val`.
static BitVec forcedVar(BitBlastEncoder& enc, unsigned w, const mpz_class& val) {
    BitVec x = enc.mkVar(w);
    enc.assertLit(enc.eq(x, enc.mkConst(val)));
    return x;
}

TEST_CASE("Stress: randomized add/sub/mul over forced-variable operands") {
    std::mt19937_64 rng(12345);
    std::uniform_int_distribution<long> dist(-1000, 1000);
    for (int iter = 0; iter < 200; ++iter) {
        long av = dist(rng), bv = dist(rng);
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec a = forcedVar(enc, 12, mpz_class(av));   // 12-bit signed covers +/-1024
        BitVec b = forcedVar(enc, 12, mpz_class(bv));
        BitVec s = enc.add(a, b);
        BitVec d = enc.sub(a, b);
        BitVec m = enc.mul(a, b);
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, s) == mpz_class(av) + mpz_class(bv));
        CHECK(readBitVec(*sat, d) == mpz_class(av) - mpz_class(bv));
        CHECK(readBitVec(*sat, m) == mpz_class(av) * mpz_class(bv));
    }
}

TEST_CASE("Stress: randomized relZero matches ground truth for all relations") {
    std::mt19937_64 rng(999);
    std::uniform_int_distribution<long> dist(-500, 500);
    for (int iter = 0; iter < 200; ++iter) {
        long kv = dist(rng);
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec x = forcedVar(enc, 11, mpz_class(kv));
        SatLit lEq  = enc.relZero(x, Relation::Eq);
        SatLit lNeq = enc.relZero(x, Relation::Neq);
        SatLit lLt  = enc.relZero(x, Relation::Lt);
        SatLit lLeq = enc.relZero(x, Relation::Leq);
        SatLit lGt  = enc.relZero(x, Relation::Gt);
        SatLit lGeq = enc.relZero(x, Relation::Geq);
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(litValue(*sat, lEq)  == (kv == 0));
        CHECK(litValue(*sat, lNeq) == (kv != 0));
        CHECK(litValue(*sat, lLt)  == (kv <  0));
        CHECK(litValue(*sat, lLeq) == (kv <= 0));
        CHECK(litValue(*sat, lGt)  == (kv >  0));
        CHECK(litValue(*sat, lGeq) == (kv >= 0));
    }
}

TEST_CASE("Stress: randomized powConst matches integer power") {
    std::mt19937_64 rng(7);
    std::uniform_int_distribution<long> base(-12, 12);
    for (int iter = 0; iter < 100; ++iter) {
        long bvl = base(rng);
        unsigned e = 1u + (static_cast<unsigned>(rng()) % 4u); // 1..4
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec x = forcedVar(enc, 6, mpz_class(bvl));
        BitVec p = enc.powConst(x, e);
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        mpz_class expected = 1;
        for (unsigned i = 0; i < e; ++i) expected *= mpz_class(bvl);
        CHECK(readBitVec(*sat, p) == expected);
    }
}

TEST_CASE("Stress: mulConst matches over random constant multipliers") {
    std::mt19937_64 rng(424242);
    std::uniform_int_distribution<long> cdist(-50, 50), xdist(-200, 200);
    for (int iter = 0; iter < 150; ++iter) {
        long cv = cdist(rng), xv = xdist(rng);
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        BitVec x = forcedVar(enc, 10, mpz_class(xv));
        BitVec r = enc.mulConst(mpz_class(cv), x);
        REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
        CHECK(readBitVec(*sat, r) == mpz_class(cv) * mpz_class(xv));
    }
}

TEST_CASE("Stress: boundary values at width extremes (incl. neg of min)") {
    for (unsigned w : {2u, 3u, 5u, 8u}) {
        mpz_class lo = -(mpz_class(1) << (w - 1));
        mpz_class hi =  (mpz_class(1) << (w - 1)) - 1;
        std::vector<mpz_class> vals = { lo, hi, mpz_class(0), mpz_class(-1), mpz_class(1) };
        for (const auto& v : vals) {
            auto sat = createSatSolver();
            BitBlastEncoder enc(*sat);
            BitVec x = forcedVar(enc, w, v);
            BitVec nx = enc.neg(x);   // width+1 so -(lo) = 2^(w-1) is representable
            REQUIRE(static_cast<int>(sat->solve()) == static_cast<int>(SatSolver::SolveResult::Sat));
            CHECK(readBitVec(*sat, x) == v);
            CHECK(readBitVec(*sat, nx) == -v);
        }
    }
}
