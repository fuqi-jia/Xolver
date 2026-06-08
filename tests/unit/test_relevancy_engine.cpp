// White-box: RelevancyEngine — z3-style boolean relevancy over the Tseitin
// skeleton. Verifies the value->relevancy propagation rules (Ite branch
// pruning, And/Or witness marking via parent revisit, Not transparency) and
// backtrackable undo. These are the subtle parts; the Atomizer extractor and
// propagator wiring are exercised by the regression suite.

#include <doctest/doctest.h>
#include "sat/RelevancyEngine.h"
#include <memory>
#include <unordered_map>

using namespace xolver;

namespace {
// A controllable value oracle: maps SatVar -> assigned bool; absent = unknown.
struct Oracle {
    std::unordered_map<SatVar, bool> vals;
    int operator()(SatVar v) const {
        auto it = vals.find(v);
        if (it == vals.end()) return 0;
        return it->second ? 1 : -1;
    }
    void set(SatVar v, bool b) { vals[v] = b; }
    void unset(SatVar v) { vals.erase(v); }
};
} // namespace

TEST_CASE("RelevancyEngine: Ite marks condition always, taken branch on demand") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t c = eng.addNode(RelKind::Leaf, /*var*/10, true);
    uint32_t t = eng.addNode(RelKind::Leaf, /*var*/11, true);
    uint32_t e = eng.addNode(RelKind::Leaf, /*var*/12, true);
    uint32_t ite = eng.addNode(RelKind::Ite, /*var*/20, true, {c, t, e});
    eng.addRoot(ite);
    eng.finalize();

    // Root + its condition relevant; branches not (condition unknown).
    CHECK(eng.isRelevantVar(20));
    CHECK(eng.isRelevantVar(10));
    CHECK_FALSE(eng.isRelevantVar(11));
    CHECK_FALSE(eng.isRelevantVar(12));

    // Decide the condition true at level 1 -> THEN branch becomes relevant.
    eng.pushLevel();
    oracle->set(10, true);
    eng.onAssign(10, true);
    CHECK(eng.isRelevantVar(11));        // then-branch now relevant
    CHECK_FALSE(eng.isRelevantVar(12));  // else-branch still pruned

    // Backtrack past the decision -> branch relevance undone, condition kept.
    eng.popToLevel(0);
    oracle->unset(10);
    CHECK_FALSE(eng.isRelevantVar(11));
    CHECK(eng.isRelevantVar(10));        // condition still relevant (level 0)
    CHECK(eng.isRelevantVar(20));
}

TEST_CASE("RelevancyEngine: Or-true marks only the satisfying disjunct") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t a = eng.addNode(RelKind::Leaf, 1, true);
    uint32_t b = eng.addNode(RelKind::Leaf, 2, true);
    uint32_t d = eng.addNode(RelKind::Leaf, 3, true);
    uint32_t orN = eng.addNode(RelKind::Or, 30, true, {a, b, d});
    eng.addRoot(orN);
    eng.finalize();

    // Assert the disjunction true; no witness yet -> no disjunct relevant.
    oracle->set(30, true);
    eng.onAssign(30, true);
    CHECK_FALSE(eng.isRelevantVar(1));
    CHECK_FALSE(eng.isRelevantVar(2));
    CHECK_FALSE(eng.isRelevantVar(3));

    // A disjunct becomes true -> exactly that disjunct is marked relevant.
    oracle->set(2, true);
    eng.onAssign(2, true);
    CHECK(eng.isRelevantVar(2));
    CHECK_FALSE(eng.isRelevantVar(1));
    CHECK_FALSE(eng.isRelevantVar(3));
}

TEST_CASE("RelevancyEngine: And-true marks all children") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t p = eng.addNode(RelKind::Leaf, 1, true);
    uint32_t q = eng.addNode(RelKind::Leaf, 2, true);
    uint32_t andN = eng.addNode(RelKind::And, 40, true, {p, q});
    eng.addRoot(andN);
    eng.finalize();

    oracle->set(40, true);
    eng.onAssign(40, true);
    CHECK(eng.isRelevantVar(1));
    CHECK(eng.isRelevantVar(2));
}

TEST_CASE("RelevancyEngine: And-false marks the false witness only") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t p = eng.addNode(RelKind::Leaf, 1, true);
    uint32_t q = eng.addNode(RelKind::Leaf, 2, true);
    uint32_t andN = eng.addNode(RelKind::And, 41, true, {p, q});
    eng.addRoot(andN);
    eng.finalize();

    oracle->set(41, false);    // conjunction false
    eng.onAssign(41, false);
    CHECK_FALSE(eng.isRelevantVar(1));  // no witness assigned yet
    CHECK_FALSE(eng.isRelevantVar(2));

    oracle->set(1, false);     // p is the false witness
    eng.onAssign(1, false);
    CHECK(eng.isRelevantVar(1));
    CHECK_FALSE(eng.isRelevantVar(2));  // q irrelevant (one witness suffices)
}

TEST_CASE("RelevancyEngine: Implies guards branch — guard always relevant, body only when guard true") {
    // The post-ITE-lowering program skeleton is a conjunction of guard->body
    // implications. Relevancy must (1) always make the GUARD decidable and
    // (2) keep the BODY irrelevant until the guard fires — this is the chained
    // pruning z3 uses to close cs_* in ~5 decisions.

    // Guard true => body becomes relevant.
    {
        RelevancyEngine eng;
        auto oracle = std::make_shared<Oracle>();
        eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });
        uint32_t g = eng.addNode(RelKind::Leaf, 1, true);   // guard
        uint32_t body = eng.addNode(RelKind::Leaf, 2, true);
        uint32_t impl = eng.addNode(RelKind::Implies, 30, true, {g, body});
        eng.addRoot(impl);
        eng.finalize();

        CHECK(eng.isRelevantVar(1));        // guard relevant immediately
        CHECK_FALSE(eng.isRelevantVar(2));  // body pruned until guard fires

        oracle->set(1, true);
        eng.onAssign(1, true);
        CHECK(eng.isRelevantVar(2));        // guard true -> body now relevant
    }

    // Guard false => body stays irrelevant (dead branch pruned).
    {
        RelevancyEngine eng;
        auto oracle = std::make_shared<Oracle>();
        eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });
        uint32_t g = eng.addNode(RelKind::Leaf, 1, true);
        uint32_t body = eng.addNode(RelKind::Leaf, 2, true);
        uint32_t impl = eng.addNode(RelKind::Implies, 31, true, {g, body});
        eng.addRoot(impl);
        eng.finalize();

        oracle->set(1, false);
        eng.onAssign(1, false);
        CHECK(eng.isRelevantVar(1));
        CHECK_FALSE(eng.isRelevantVar(2));  // body never reached
    }
}

TEST_CASE("RelevancyEngine: Not is transparent to its operand") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t a = eng.addNode(RelKind::Leaf, 1, true);
    uint32_t b = eng.addNode(RelKind::Leaf, 2, true);
    uint32_t orN = eng.addNode(RelKind::Or, 50, true, {a, b});
    uint32_t notN = eng.addNode(RelKind::Not, 51, true, {orN});
    eng.addRoot(notN);
    eng.finalize();

    // Not relevant => operand (the Or) relevant immediately, even unvalued.
    CHECK(eng.isRelevantVar(50));
}

TEST_CASE("RelevancyEngine: pickRelevantUnassigned returns a relevant, unassigned var") {
    RelevancyEngine eng;
    auto oracle = std::make_shared<Oracle>();
    eng.setValueOracle([oracle](SatVar v) { return (*oracle)(v); });

    uint32_t c = eng.addNode(RelKind::Leaf, 10, true);
    uint32_t t = eng.addNode(RelKind::Leaf, 11, true);
    uint32_t e = eng.addNode(RelKind::Leaf, 12, true);
    uint32_t ite = eng.addNode(RelKind::Ite, 20, true, {c, t, e});
    eng.addRoot(ite);
    eng.finalize();

    // Relevant unassigned vars are {20 (ite), 10 (cond)}. 11/12 are irrelevant.
    SatVar pick = eng.pickRelevantUnassigned();
    CHECK((pick == 10 || pick == 20));

    // Assign both relevant vars -> nothing relevant+unassigned -> 0 (decline).
    oracle->set(10, true);
    oracle->set(20, true);
    eng.onAssign(20, true);
    eng.onAssign(10, true);
    // Now 11 (then) is relevant but unassigned -> it should be returned.
    SatVar pick2 = eng.pickRelevantUnassigned();
    CHECK(pick2 == 11);
}
