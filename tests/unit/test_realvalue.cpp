// RealValue unit tests — Phase 1 (live).
//
// Exercises the unified Real value type (src/util/RealValue.h): rational
// fast-path arithmetic, libpoly-delegated algebraic arithmetic (√2, √3),
// mixed-kind total-order comparison, sign from a touching interval,
// algebraic-integer floor/ceil, and toSmtLib2↔parse round-trips. These run by
// default (the Phase-0 doctest::skip decorators were removed once RealValue was
// implemented).

#include <doctest/doctest.h>
#include "util/RealValue.h"

#include <gmpxx.h>
#include <stdexcept>

using namespace nlcolver;

namespace {

// √2 : real root of x² − 2 in [1, 2].
AlgebraicNumber sqrt2() {
    return AlgebraicNumber{{mpz_class(-2), mpz_class(0), mpz_class(1)},
                           mpq_class(1), mpq_class(2), true, true};
}
// √3 : real root of x² − 3 in [1, 2].
AlgebraicNumber sqrt3() {
    return AlgebraicNumber{{mpz_class(-3), mpz_class(0), mpz_class(1)},
                           mpq_class(1), mpq_class(2), true, true};
}
// 5 expressed algebraically: root of x − 5 in [4, 6].
AlgebraicNumber five() {
    return AlgebraicNumber{{mpz_class(-5), mpz_class(1)},
                           mpq_class(4), mpq_class(6), true, true};
}

}  // namespace

TEST_SUITE("realvalue") {

TEST_CASE("RealValue: rational constructors round-trip") {
    RealValue a = RealValue::fromInt(7);
    CHECK(a.isRational());
    CHECK(a.asRational() == mpq_class(7));

    RealValue b = RealValue::fromMpq(mpq_class(3, 4));
    CHECK(b.isRational());
    CHECK(b.asRational() == mpq_class(3, 4));

    RealValue c = RealValue::fromMpz(mpz_class(-12));
    CHECK(c.asRational() == mpq_class(-12));
}

TEST_CASE("RealValue: parse canonical literals") {
    CHECK(RealValue::parse("3").asRational() == mpq_class(3));
    CHECK(RealValue::parse("(/ 3 4)").asRational() == mpq_class(3, 4));
    CHECK(RealValue::parse("(- (/ 3 4))").asRational() == mpq_class(-3, 4));
}

TEST_CASE("RealValue: rational arithmetic stays rational") {
    RealValue a = RealValue::fromMpq(mpq_class(1, 2));
    RealValue b = RealValue::fromMpq(mpq_class(1, 3));
    CHECK((a + b).isRational());
    CHECK((a + b).asRational() == mpq_class(5, 6));
    CHECK((a - b).asRational() == mpq_class(1, 6));
    CHECK((a * b).asRational() == mpq_class(1, 6));
    CHECK((a / b).asRational() == mpq_class(3, 2));
    CHECK((-a).asRational() == mpq_class(-1, 2));
}

TEST_CASE("RealValue: division by zero throws") {
    RealValue a = RealValue::fromInt(1);
    RealValue z = RealValue::fromInt(0);
    CHECK_THROWS_AS(a / z, std::domain_error);
}

TEST_CASE("RealValue: algebraic construction") {
    RealValue r2 = RealValue::fromAlgebraic(sqrt2());
    CHECK(r2.isAlgebraic());
    CHECK_FALSE(r2.isRational());
    CHECK(r2.sign() == 1);
}

TEST_CASE("RealValue: rational ⊕ algebraic promotes to algebraic") {
    RealValue one = RealValue::fromInt(1);
    RealValue r2 = RealValue::fromAlgebraic(sqrt2());      // ≈ 1.4142
    RealValue s = one + r2;                                // ≈ 2.4142
    CHECK(s.isAlgebraic());
    CHECK(s.compare(RealValue::fromInt(2)) == 1);          // 1+√2 > 2
    CHECK(s.compare(RealValue::fromInt(3)) == -1);         // 1+√2 < 3
}

TEST_CASE("RealValue: algebraic ⊕ algebraic (√2 + √3)") {
    RealValue sum = RealValue::fromAlgebraic(sqrt2()) + RealValue::fromAlgebraic(sqrt3());
    CHECK(sum.isAlgebraic());                              // ≈ 3.1463
    CHECK(sum.compare(RealValue::fromInt(3)) == 1);
    CHECK(sum.compare(RealValue::fromInt(4)) == -1);
}

TEST_CASE("RealValue: mixed comparison total order") {
    RealValue r2 = RealValue::fromAlgebraic(sqrt2());      // ≈ 1.4142
    RealValue threeHalves = RealValue::fromMpq(mpq_class(3, 2));  // 1.5
    CHECK(r2.compare(threeHalves) == -1);                  // √2 < 3/2
    CHECK(threeHalves.compare(r2) == 1);
    CHECK(r2.compare(r2) == 0);
}

TEST_CASE("RealValue: sign from a touching interval") {
    // √2 isolated by [0, 2] (lower touches 0); sign() must refine to +.
    AlgebraicNumber a = sqrt2();
    a.lower = mpq_class(0);
    CHECK(RealValue::fromAlgebraic(a).sign() == 1);
}

TEST_CASE("RealValue: algebraic integer (root of x − 5)") {
    RealValue v = RealValue::fromAlgebraic(five());
    CHECK(v.isExactInteger());
    CHECK(v.floor() == mpz_class(5));
    CHECK(v.ceil() == mpz_class(5));
}

TEST_CASE("RealValue: toSmtLib2 round-trips via parse (rational)") {
    RealValue q = RealValue::fromMpq(mpq_class(-7, 5));
    RealValue back = RealValue::parse(q.toSmtLib2());
    CHECK(back.compare(q) == 0);
}

TEST_CASE("ExtendedRealValue: infinities order correctly") {
    ExtendedRealValue ninf = ExtendedRealValue::negInf();
    ExtendedRealValue pinf = ExtendedRealValue::posInf();
    ExtendedRealValue zero = ExtendedRealValue::finite(RealValue::fromInt(0));
    CHECK(ninf.compare(zero) == -1);
    CHECK(zero.compare(pinf) == -1);
    CHECK(ninf.compare(pinf) == -1);
    CHECK(pinf.compare(pinf) == 0);
}

}  // TEST_SUITE("realvalue")
