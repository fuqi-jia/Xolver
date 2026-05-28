// CAC covering data structures (module A — src/theory/arith/nra/cac/CacCovering).
// Exact open/closed/±∞ interval union: membership, gap-sampling, completeness,
// and a rational strictly between two reals (incl. algebraic endpoints).

#include <doctest/doctest.h>
#include <gmpxx.h>
#include "theory/arith/nra/cac/Covering.h"

using namespace xolver;

static RealValue Q(long n, long d = 1) { return RealValue::fromMpq(mpq_class(n, d)); }
static ExtendedRealValue F(long n, long d = 1) { return ExtendedRealValue::finite(Q(n, d)); }

// √2 as an algebraic value: root of x^2 - 2 isolated in (1, 2).
static RealValue sqrt2() {
    AlgebraicNumber a;
    a.coefficients = {mpz_class(-2), mpz_class(0), mpz_class(1)};
    a.lower = mpq_class(1); a.upper = mpq_class(2);
    a.lowerOpen = true; a.upperOpen = true;
    return RealValue::fromAlgebraic(std::move(a));
}

static CacInterval openIv(long lo, long hi) {
    return CacInterval::make(F(lo), F(hi), true, true);
}

TEST_CASE("CacInterval: contains open/closed/inf") {
    auto oo = CacInterval::make(F(0), F(2), true, true);    // (0,2)
    CHECK_FALSE(oo.contains(Q(0)));
    CHECK(oo.contains(Q(1)));
    CHECK_FALSE(oo.contains(Q(2)));

    auto cc = CacInterval::make(F(0), F(2), false, false);  // [0,2]
    CHECK(cc.contains(Q(0)));
    CHECK(cc.contains(Q(2)));

    auto right = CacInterval::make(ExtendedRealValue::negInf(), F(2), true, true); // (-inf,2)
    CHECK(right.contains(Q(-1000)));
    CHECK_FALSE(right.contains(Q(2)));

    auto pt = CacInterval::point(Q(5));
    CHECK(pt.contains(Q(5)));
    CHECK_FALSE(pt.contains(Q(4)));
}

TEST_CASE("CacCovering: empty samples 0, not complete") {
    CacCovering c;
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK(s->compare(Q(0)) == 0);
    CHECK_FALSE(c.isComplete());
}

TEST_CASE("CacCovering: full line is complete, no sample") {
    CacCovering c;
    c.add(CacInterval::all());
    CHECK(c.isComplete());
    CHECK_FALSE(c.sampleUncovered().has_value());
}

TEST_CASE("CacCovering: two halves closed at the join cover ℝ") {
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(), F(1), true, false)); // (-inf,1]
    c.add(CacInterval::make(F(1), ExtendedRealValue::posInf(), false, true)); // [1,+inf)
    CHECK(c.isComplete());
    CHECK_FALSE(c.sampleUncovered().has_value());
}

TEST_CASE("CacCovering: two halves both open at the join leave a point gap") {
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(), F(1), true, true));  // (-inf,1)
    c.add(CacInterval::make(F(1), ExtendedRealValue::posInf(), true, true));  // (1,+inf)
    CHECK_FALSE(c.isComplete());
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK(s->compare(Q(1)) == 0);            // the uncovered point is exactly 1
    CHECK_FALSE(c.covers(Q(1)));
}

TEST_CASE("CacCovering: interior open gap yields a rational inside it") {
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(), F(0), true, true));  // (-inf,0)
    c.add(CacInterval::make(F(3), ExtendedRealValue::posInf(), true, true));  // (3,+inf)
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK(s->compare(Q(0)) > 0);
    CHECK(s->compare(Q(3)) < 0);
    CHECK_FALSE(c.covers(*s));
}

TEST_CASE("CacCovering: left and right gaps") {
    CacCovering c;
    c.add(openIv(0, 5));                      // only (0,5) excluded
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK_FALSE(c.covers(*s));                // some point outside (0,5)
    // overlapping intervals merge; still leaves gaps on both sides
    c.add(openIv(4, 10));                     // union (0,10)
    auto s2 = c.sampleUncovered();
    REQUIRE(s2.has_value());
    CHECK_FALSE(c.covers(*s2));
}

TEST_CASE("CacCovering: overlapping intervals merge to cover ℝ") {
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(), F(2), true, true));  // (-inf,2)
    c.add(CacInterval::make(F(1), ExtendedRealValue::posInf(), true, true));  // (1,+inf) overlap (1,2)
    CHECK(c.isComplete());
}

TEST_CASE("rationalStrictlyBetween: rationals") {
    auto q = rationalStrictlyBetween(Q(1), Q(2));
    CHECK(RealValue::fromMpq(q).compare(Q(1)) > 0);
    CHECK(RealValue::fromMpq(q).compare(Q(2)) < 0);
}

TEST_CASE("rationalStrictlyBetween: algebraic endpoint (√2, 2)") {
    RealValue s2 = sqrt2();
    auto q = rationalStrictlyBetween(s2, Q(2));
    RealValue qv = RealValue::fromMpq(q);
    CHECK(qv.compare(s2) > 0);     // q > √2
    CHECK(qv.compare(Q(2)) < 0);   // q < 2
}

TEST_CASE("rationalStrictlyBetween: rational below an algebraic (1, √2)") {
    RealValue s2 = sqrt2();
    auto q = rationalStrictlyBetween(Q(1), s2);
    RealValue qv = RealValue::fromMpq(q);
    CHECK(qv.compare(Q(1)) > 0);   // q > 1
    CHECK(qv.compare(s2) < 0);     // q < √2
}

TEST_CASE("CacCovering: point-gap at a shared ALGEBRAIC open endpoint (√2)") {
    // (-inf, √2) and (√2, +inf), both OPEN at √2 → the point √2 is uncovered.
    // This is the false-UNSAT shape (x^2=2 ∧ x>0: the SAT point √2 is a shared
    // open boundary). sampleUncovered MUST return √2, and √2 MUST be uncovered.
    RealValue s2a = sqrt2();   // two independent √2 constructions (as in two
    RealValue s2b = sqrt2();   // separate intervalFromCharacterization calls)
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(),
                            ExtendedRealValue::finite(s2a), true, true));
    c.add(CacInterval::make(ExtendedRealValue::finite(s2b),
                            ExtendedRealValue::posInf(), true, true));
    CHECK_FALSE(c.isComplete());
    CHECK_FALSE(c.covers(sqrt2()));
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK(s->compare(sqrt2()) == 0);   // the uncovered point is exactly √2
}

TEST_CASE("CacCovering: algebraic endpoints — gap sampled between two roots") {
    // Exclude (-inf, √2) and (2, +inf); the gap [√2, 2] (minus the open √2) must
    // yield a covered-checked sample strictly between √2 and 2.
    RealValue s2 = sqrt2();
    CacCovering c;
    c.add(CacInterval::make(ExtendedRealValue::negInf(),
                            ExtendedRealValue::finite(s2), true, true));     // (-inf,√2)
    c.add(CacInterval::make(F(2), ExtendedRealValue::posInf(), true, true)); // (2,+inf)
    auto s = c.sampleUncovered();
    REQUIRE(s.has_value());
    CHECK_FALSE(c.covers(*s));
    CHECK(s->compare(s2) >= 0);
    CHECK(s->compare(Q(2)) <= 0);
}
