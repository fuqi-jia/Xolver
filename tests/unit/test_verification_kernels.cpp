#include <doctest/doctest.h>
#include "evidence/PresburgerCertificate.h"
#include "evidence/HeapCertificate.h"

using namespace xolver;
using namespace xolver::proof;

TEST_CASE("Presburger certificates: check cancellation, signs and exact arithmetic") {
    // x <= 0 and x >= 1.
    std::vector<IntegerInequality> p{{{{0, 1}}, 0}, {{{0, -1}}, -1}};
    CHECK(checkIntegerLinearContradiction(p, {1, 1}));
    CHECK_FALSE(checkIntegerLinearContradiction(p, {1, -1}));
    CHECK_FALSE(checkIntegerLinearContradiction(p, {1, 0}));
    CHECK_FALSE(checkIntegerLinearContradiction(p, {1}));
    mpz_class big("100000000000000000000000000000000000000001");
    CHECK(checkIntegerLinearContradiction(p, {big, big}));
    p[1].bound = 0; // x=0 is now a witness.
    CHECK_FALSE(checkIntegerLinearContradiction(p, {big, big}));
}

TEST_CASE("Presburger certificates: negative-bound rounding agrees with integer semantics") {
    for (int a = 1; a <= 9; ++a) {
        for (int b = -15; b <= 15; ++b) {
            const int floor = b >= 0 ? b / a : -((-b + a - 1) / a);
            IntegerInequality premise{{{0, a}}, b}, conclusion{{{0, 1}}, floor};
            CHECK(checkIntegerGcdTightening(premise, conclusion));
            conclusion.bound += 1;
            CHECK_FALSE(checkIntegerGcdTightening(premise, conclusion));
            for (int x = -20; x <= 20; ++x)
                CHECK((a * x <= b) == (x <= floor));
        }
    }
    CHECK(checkIntegerEqualityContradiction({{0, 6}, {1, 10}}, 3));
    CHECK_FALSE(checkIntegerEqualityContradiction({{0, 6}, {1, 10}}, 4));
    CHECK(checkIntegerEqualityContradiction({}, 1));
    CHECK_FALSE(checkIntegerEqualityContradiction({}, 0));
    CHECK_FALSE(checkIntegerEqualityContradiction({{NullVar, 2}}, 1));
}

TEST_CASE("Heap certificates: emp, nil, disjointness and exact footprint") {
    HeapRecord record{HeapLocation{0}, mpz_class(7)};
    FiniteHeap h{{HeapLocation{1}, record}, {HeapLocation{2}, record}};
    CHECK(checkGroundSymbolicHeap({}, {}));
    CHECK_FALSE(checkGroundSymbolicHeap(h, {}));
    CHECK(checkGroundSymbolicHeap(h, {{{1}, record}, {{2}, record}}));
    CHECK_FALSE(checkGroundSymbolicHeap(h, {{{1}, record}, {{1}, record}}));
    CHECK_FALSE(checkGroundSymbolicHeap({{{0}, record}}, {{{0}, record}}));
    CHECK(checkHeapPartition(h, {{{{1}, record}}, {{{2}, record}}}));
    CHECK_FALSE(checkHeapPartition(h, {h, h}));
    CHECK_FALSE(checkHeapPartition(h, {{{{1}, record}}}));
    CHECK_FALSE(checkHeapPartition(h, {{{{1}, {mpz_class(9)}}}, {{{2}, record}}}));
    CHECK_FALSE(checkGroundSymbolicHeap({{{1}, {HeapLocation{2}}}}, {{{1}, {mpz_class(2)}}}));
}

TEST_CASE("Heap certificates: enumerate finite alias arrangements") {
    // Independent reference condition for pto(x,7) * pto(y,8).
    for (uint64_t x = 0; x < 4; ++x) {
        for (uint64_t y = 0; y < 4; ++y) {
            FiniteHeap h;
            h[{x}] = {mpz_class(7)};
            h[{y}] = {mpz_class(8)};
            CHECK(checkGroundSymbolicHeap(h, {{{x}, {mpz_class(7)}}, {{y}, {mpz_class(8)}}}) ==
                  (x != 0 && y != 0 && x != y));
        }
    }
}
