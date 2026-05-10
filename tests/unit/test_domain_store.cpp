#include <doctest/doctest.h>
#include "theory/arith/nia/DomainStore.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>

using namespace nlcolver;

// Helper: create a positive SatLit as a dummy reason
static SatLit reason(SatVar v) { return SatLit::positive(v); }

TEST_CASE("DomainStore: bounds conflict x>=5 and x<=3") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(5), reason(1));
    ds.addUpperBound("x", mpz_class(3), reason(2));
    CHECK(ds.isEmpty("x"));
    CHECK(ds.isEmpty());

    auto conflict = ds.buildEmptyDomainConflict();
    REQUIRE(!conflict.clause.empty());
    // Clause should contain negated reasons
    bool hasR1 = false, hasR2 = false;
    for (const auto& lit : conflict.clause) {
        if (lit.var == 1 && !lit.sign) hasR1 = true;
        if (lit.var == 2 && !lit.sign) hasR2 = true;
    }
    CHECK(hasR1);
    CHECK(hasR2);
}

TEST_CASE("DomainStore: finite set disjoint from bounds") {
    DomainStore ds;
    ds.restrictToFiniteSet("x", {mpz_class(1), mpz_class(2), mpz_class(3)}, reason(1));
    ds.addLowerBound("x", mpz_class(4), reason(2));
    CHECK(ds.isEmpty("x"));

    auto conflict = ds.buildEmptyDomainConflict();
    REQUIRE(!conflict.clause.empty());
    bool hasR1 = false, hasR2 = false;
    for (const auto& lit : conflict.clause) {
        if (lit.var == 1 && !lit.sign) hasR1 = true;
        if (lit.var == 2 && !lit.sign) hasR2 = true;
    }
    CHECK(hasR1);
    CHECK(hasR2);
}

TEST_CASE("DomainStore: exclusions exhaust bounded range") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), reason(1));
    ds.addUpperBound("x", mpz_class(2), reason(2));
    ds.excludeValue("x", mpz_class(0), reason(3));
    ds.excludeValue("x", mpz_class(1), reason(4));
    ds.excludeValue("x", mpz_class(2), reason(5));
    CHECK(ds.isEmpty("x"));

    auto conflict = ds.buildEmptyDomainConflict();
    REQUIRE(!conflict.clause.empty());
    bool hasR1 = false, hasR2 = false;
    for (const auto& lit : conflict.clause) {
        if (lit.var == 1 && !lit.sign) hasR1 = true;
        if (lit.var == 2 && !lit.sign) hasR2 = true;
    }
    CHECK(hasR1);
    CHECK(hasR2);
}

TEST_CASE("DomainStore: finite set intersection") {
    DomainStore ds;
    ds.restrictToFiniteSet("x", {mpz_class(1), mpz_class(2), mpz_class(3)}, reason(1));
    ds.restrictToFiniteSet("x", {mpz_class(2), mpz_class(3), mpz_class(4)}, reason(2));
    CHECK(!ds.isEmpty("x"));

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    REQUIRE(d->finiteValues.has_value());
    CHECK(d->finiteValues->size() == 2);
    CHECK(d->finiteValues->count(mpz_class(2)));
    CHECK(d->finiteValues->count(mpz_class(3)));
}

TEST_CASE("DomainStore: weaker bound ignored, stronger bound replaces reason") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), reason(1));
    ds.addLowerBound("x", mpz_class(3), reason(2));

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->lower.value == 3);
    CHECK(d->lower.reasons.size() == 1);
    CHECK(d->lower.reasons[0].var == 2);
}

TEST_CASE("DomainStore: same bound accumulates reasons") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(5), reason(1));
    ds.addLowerBound("x", mpz_class(5), reason(2));

    const IntDomain* d = ds.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->lower.value == 5);
    CHECK(d->lower.reasons.size() == 2);
}

TEST_CASE("DomainStore: totalSize with finite set") {
    DomainStore ds;
    ds.restrictToFiniteSet("x", {mpz_class(1), mpz_class(2), mpz_class(3)}, reason(1));
    ds.addLowerBound("y", mpz_class(0), reason(2));
    ds.addUpperBound("y", mpz_class(2), reason(3));
    mpz_class sz = ds.totalSize({"x", "y"});
    CHECK(sz == 9); // 3 * 3
}

TEST_CASE("DomainStore: totalSize with exclusions") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), reason(1));
    ds.addUpperBound("x", mpz_class(2), reason(2));
    ds.excludeValue("x", mpz_class(1), reason(3));
    mpz_class sz = ds.totalSize({"x"});
    CHECK(sz == 2); // {0, 2}
}

TEST_CASE("DomainStore: allFinite requires both bounds or finite set") {
    DomainStore ds;
    ds.addLowerBound("x", mpz_class(0), reason(1));
    CHECK(!ds.allFinite({"x"}));
    ds.addUpperBound("x", mpz_class(5), reason(2));
    CHECK(ds.allFinite({"x"}));
}

TEST_CASE("DomainStore: finite set fully excluded -> empty") {
    DomainStore ds;
    ds.restrictToFiniteSet("x", {mpz_class(1), mpz_class(2), mpz_class(3)}, reason(1));
    ds.excludeValue("x", mpz_class(1), reason(2));
    ds.excludeValue("x", mpz_class(2), reason(3));
    ds.excludeValue("x", mpz_class(3), reason(4));
    CHECK(ds.isEmpty("x"));
    CHECK(ds.isEmpty());

    auto conflict = ds.buildEmptyDomainConflict();
    REQUIRE(!conflict.clause.empty());
    // Should contain negated reasons from finite set and exclusions
    bool hasR1 = false;
    for (const auto& lit : conflict.clause) {
        if (lit.var == 1 && !lit.sign) hasR1 = true;
    }
    CHECK(hasR1);
}
