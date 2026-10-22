#include <doctest/doctest.h>
#include "search/nia/core/DomainStore.h"
#include <algorithm>
#include <set>

using namespace xolver;

namespace {
SatLit reason(int n) { return SatLit::positive(n); }
bool has(const std::vector<SatLit>& reasons, int n) {
    return std::find(reasons.begin(), reasons.end(), reason(n)) != reasons.end();
}
std::set<mpz_class> values(unsigned mask) {
    std::set<mpz_class> result;
    for (unsigned v = 0; v != 4; ++v) if ((mask >> v) & 1U) result.emplace(v);
    return result;
}
bool member(unsigned mask, int x) {
    return x >= 0 && x < 4 && ((mask >> x) & 1U);
}
}

TEST_CASE("DomainStore explanations: intersection lower bound retains earlier set") {
    DomainStore store;
    store.restrictToFiniteSet("x", {1, 3}, reason(1));
    store.restrictToFiniteSet("x", {2, 3}, reason(2));
    store.addUpperBound("x", 2, reason(3));
    REQUIRE(store.isEmpty());
    auto conflict = store.buildEmptyDomainConflict();
    // Reasons 2 and 3 alone admit x=2. Reason 1 is necessary to refute it.
    CHECK(has(conflict.clause, 1));
    CHECK(has(conflict.clause, 2));
    CHECK(has(conflict.clause, 3));
}

TEST_CASE("DomainStore explanations: intersection upper bound retains earlier set") {
    DomainStore store;
    store.restrictToFiniteSet("x", {1, 3}, reason(1));
    store.restrictToFiniteSet("x", {1, 2}, reason(2));
    store.addLowerBound("x", 2, reason(3));
    REQUIRE(store.isEmpty());
    auto conflict = store.buildEmptyDomainConflict();
    CHECK(has(conflict.clause, 1));
    CHECK(has(conflict.clause, 2));
    CHECK(has(conflict.clause, 3));
}

TEST_CASE("DomainStore explanations: emitted reasons independently refute finite witnesses") {
    for (unsigned a = 1; a < 16; ++a) {
        for (unsigned b = 1; b < 16; ++b) {
            for (int cut = 0; cut < 4; ++cut) {
                for (bool upper : {false, true}) {
                    CAPTURE(a); CAPTURE(b); CAPTURE(cut); CAPTURE(upper);
                    DomainStore store;
                    store.restrictToFiniteSet("x", values(a), reason(1));
                    store.restrictToFiniteSet("x", values(b), reason(2));
                    if (upper) store.addUpperBound("x", cut, reason(3));
                    else store.addLowerBound("x", cut, reason(3));
                    if (!store.isEmpty()) continue;
                    const auto conflict = store.buildEmptyDomainConflict();
                    REQUIRE(!conflict.clause.empty());
                    // Include points outside both finite sets: an explanation
                    // omitting their reasons must still refute those points.
                    for (int x = -1; x <= 4; ++x) {
                        bool allReasonsHold = true;
                        for (const auto& literal : conflict.clause) {
                            REQUIRE(literal.var >= 1);
                            REQUIRE(literal.var <= 3);
                            bool truth = literal.var == 1 ? member(a, x)
                                : literal.var == 2 ? member(b, x)
                                : upper ? x <= cut : x >= cut;
                            allReasonsHold &= literal.sign ? truth : !truth;
                        }
                        CHECK_FALSE(allReasonsHold);
                    }
                }
            }
        }
    }
}
