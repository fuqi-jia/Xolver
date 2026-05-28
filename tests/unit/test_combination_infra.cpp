#include <doctest/doctest.h>
#include "theory/combination/ConflictMinimizer.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include <cstdlib>

using namespace xolver;

TEST_CASE("ConflictMinimizer: dedup removes exact-duplicate literals only") {
    std::vector<SatLit> lits = {
        {3, true}, {1, false}, {3, true}, {1, false}, {2, true}
    };
    ConflictMinimizer::dedup(lits);
    REQUIRE(lits.size() == 3);
    // Deterministic order: by var, then sign.
    CHECK(lits[0] == SatLit{1, false});
    CHECK(lits[1] == SatLit{2, true});
    CHECK(lits[2] == SatLit{3, true});
}

TEST_CASE("ConflictMinimizer: complementary literals are kept (meaning preserved)") {
    std::vector<SatLit> lits = {{5, true}, {5, false}};
    ConflictMinimizer::dedup(lits);
    CHECK(lits.size() == 2);  // x and ¬x are distinct literals — never merged
}

TEST_CASE("ConflictMinimizer: empty and singleton are no-ops") {
    std::vector<SatLit> empty;
    ConflictMinimizer::dedup(empty);
    CHECK(empty.empty());
    std::vector<SatLit> one = {{7, true}};
    ConflictMinimizer::dedup(one);
    CHECK(one.size() == 1);
}

namespace {
TheoryLemma mkLemma(SatVar v) { return TheoryLemma{{SatLit{v, true}}}; }
}

TEST_CASE("TheoryLemmaDatabase: unbounded dedup when flag OFF") {
    unsetenv("XOLVER_SAT_LEMMA_MGMT");  // hermetic: assert true flag-OFF behavior
    TheoryLemmaDatabase db;
    CHECK(db.insertIfNew(mkLemma(1)));
    CHECK_FALSE(db.insertIfNew(mkLemma(1)));  // dedup
    CHECK(db.contains(mkLemma(1)));
    for (SatVar v = 2; v <= 1000; ++v) CHECK(db.insertIfNew(mkLemma(v)));
    CHECK(db.contains(mkLemma(1)));   // nothing evicted (cap 0)
    CHECK(db.contains(mkLemma(1000)));
}

TEST_CASE("TheoryLemmaDatabase: FIFO eviction under XOLVER_SAT_LEMMA_MGMT") {
    setenv("XOLVER_SAT_LEMMA_MGMT", "3", 1);
    TheoryLemmaDatabase db;
    for (SatVar v = 1; v <= 3; ++v) CHECK(db.insertIfNew(mkLemma(v)));
    CHECK(db.contains(mkLemma(1)));
    CHECK(db.contains(mkLemma(3)));

    // 4th insert evicts the oldest (lemma 1); recent ones survive.
    CHECK(db.insertIfNew(mkLemma(4)));
    CHECK_FALSE(db.contains(mkLemma(1)));  // evicted
    CHECK(db.contains(mkLemma(2)));
    CHECK(db.contains(mkLemma(3)));
    CHECK(db.contains(mkLemma(4)));

    // Re-inserting an evicted lemma is "new" again (sound re-derivation path),
    // and now evicts the next-oldest (lemma 2).
    CHECK(db.insertIfNew(mkLemma(1)));
    CHECK_FALSE(db.contains(mkLemma(2)));
    CHECK(db.contains(mkLemma(1)));
    unsetenv("XOLVER_SAT_LEMMA_MGMT");
}
