#include <doctest/doctest.h>
#include "search/combination/ConflictMinimizer.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "contracts/TheoryAtomTypes.h"
#include "search/coordination/TheoryManager.h"
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

TEST_CASE("TheoryLemmaDatabase: exact clauses and installation are distinct") {
    TheoryLemmaDatabase db;
    TheoryLemma a{{{1, true}, {2, false}}};
    TheoryLemma reordered{{{2, false}, {1, true}, {1, true}}};
    TheoryLemma opposite{{{1, true}, {2, true}}};
    CHECK(db.insertIfNew(a));
    CHECK_FALSE(db.insertIfNew(reordered));
    CHECK_FALSE(db.isInstalled(a));
    CHECK_FALSE(db.contains(opposite));
    db.markInstalled(reordered);
    CHECK(db.isInstalled(a));
    CHECK_FALSE(db.isInstalled(opposite));
    CHECK(db.insertIfNew(opposite));
    CHECK(db.insertIfNew(TheoryLemma{}));
    CHECK(db.contains(TheoryLemma{}));
}

namespace {
struct CandidateTheory : TheorySolver {
    TheoryCheckResult next = TheoryCheckResult::consistent();
    int publications = 0;
    TheoryId id() const override { return TheoryId::EUF; }
    void push() override {}
    void pop(uint32_t) override {}
    void assertLit(const TheoryAtomRecord&, bool, int, SatLit) override {}
    void backtrackToLevel(int) override {}
    void reset() override {}
    TheoryCheckResult check(TheoryLemmaStorage&, TheoryEffort) override { return next; }
    std::vector<SharedEqualityPropagation> getDeducedSharedEqualities() override {
        ++publications;
        return {};
    }
};
struct CandidateAssignment : TheoryAssignmentView {
    LitValue value(SatLit) const override { return LitValue::True; }
};
} // namespace

TEST_CASE("Combination candidate: only a complete accepted witness stops Full search") {
    TheoryManager manager;
    manager.setCombinationMode(true);
    auto theory = std::make_unique<CandidateTheory>();
    manager.registerSolver(std::move(theory));
    CandidateAssignment assignment;
    manager.setAssignmentView(&assignment);
    TheoryLemmaDatabase lemmas;
    int checks = 0;
    bool accept = false;
    manager.setModelCandidateCheck([&](const TheoryAssignmentView& view) {
        ++checks;
        CHECK(view.value({1, true}) == LitValue::True);
        return accept;
    });
    CHECK(manager.check(lemmas, TheoryEffort::Standard).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(checks == 0);
    CHECK(manager.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(checks == 1);
    accept = true;
    const auto completed = manager.check(lemmas, TheoryEffort::Full);
    CHECK(completed.kind == TheoryCheckResult::Kind::Unknown);
    CHECK(completed.reason == "validated original-query witness");
    CHECK(checks == 2);

    // A missing assignment view cannot certify a full candidate.
    manager.setAssignmentView(nullptr);
    CHECK(manager.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(checks == 2);
    manager.clearSolvers();
    manager.setAssignmentView(&assignment);
    CHECK(manager.check(lemmas, TheoryEffort::Full).kind == TheoryCheckResult::Kind::Consistent);
    CHECK(checks == 2);
}

TEST_CASE("Combination candidate: unresolved theory results retain their original obligation") {
    for (const auto pending : {TheoryCheckResult::unknown("pending theory"),
                              TheoryCheckResult::mkLemma(TheoryLemma{{{1, true}}}),
                              TheoryCheckResult::mkConflict(TheoryConflict{{{1, true}}})}) {
        TheoryManager manager;
        manager.setCombinationMode(true);
        auto theory = std::make_unique<CandidateTheory>();
        theory->next = pending;
        manager.registerSolver(std::move(theory));
        CandidateAssignment assignment;
        manager.setAssignmentView(&assignment);
        int checks = 0;
        manager.setModelCandidateCheck([&](const TheoryAssignmentView&) { ++checks; return true; });
        TheoryLemmaDatabase lemmas;
        CHECK(manager.check(lemmas, TheoryEffort::Full).kind == pending.kind);
        CHECK(checks == 0);
    }
}
