#include <doctest/doctest.h>
#include "theory/arith/ArithSolverBase.h"
#include "theory/core/TheoryLemmaDatabase.h"

using namespace xolver;

namespace {

// Minimal mock subclass exposing the protected state for assertions and
// recording hook invocations.
class MockArithSolver : public ArithSolverBase {
public:
    TheoryId id() const override { return TheoryId::LIA; }

    TheoryCheckResult check(TheoryLemmaStorage&,
                            TheoryEffort = TheoryEffort::Standard) override {
        if (hasPending()) return drainPending();
        return TheoryCheckResult::consistent();
    }

    // Expose protected internals for the test.
    size_t trailSize() const { return state_.trail.size(); }
    int currentLevel() const { return state_.currentLevel; }
    ScopeLevel scopeLevel() const { return state_.scopeLevel; }
    bool pending() const { return hasPending(); }

    void doRecordConflict(int level, std::vector<SatLit> lits) {
        recordPending(level, TheoryCheckResult::mkConflict(TheoryConflict{std::move(lits)}));
    }
    void doRecordUnknown(int level) {
        recordPending(level, TheoryCheckResult::unknown("mock"));
    }

    int assertCount = 0;
    int backtrackCount = 0;
    int resetCount = 0;
    int pushCount = 0;
    int popCount = 0;

protected:
    void onAssertLit(const TheoryAtomRecord&, bool, int, SatLit) override { ++assertCount; }
    void onBacktrack(int) override { ++backtrackCount; }
    void onReset() override { ++resetCount; }
    void onPush() override { ++pushCount; }
    void onPop(uint32_t) override { ++popCount; }
};

TheoryAtomRecord mkAtom(SatVar v) {
    TheoryAtomRecord r;
    r.satVar = v;
    r.theory = TheoryId::LIA;
    r.isDynamic = false;
    r.exprId = NullExpr;
    r.payload = LinearAtomPayload{};
    return r;
}

} // namespace

TEST_CASE("ArithSolverBase: assertLit appends and dedups by satVar") {
    MockArithSolver s;
    TheoryLemmaDatabase db;

    s.assertLit(mkAtom(1), true, 1, SatLit::positive(1));
    s.assertLit(mkAtom(2), true, 1, SatLit::positive(2));
    CHECK(s.trailSize() == 2);
    CHECK(s.assertCount == 2);

    // Re-asserting satVar 1 with a new value REPLACES, doesn't append.
    s.assertLit(mkAtom(1), false, 2, SatLit::negative(1));
    CHECK(s.trailSize() == 2);          // still 2 entries
    CHECK(s.assertCount == 3);          // hook still fired
    CHECK(s.currentLevel() == 2);
}

TEST_CASE("ArithSolverBase: backtrackToLevel removes entries above target") {
    MockArithSolver s;

    s.assertLit(mkAtom(1), true, 1, SatLit::positive(1));
    s.assertLit(mkAtom(2), true, 2, SatLit::positive(2));
    s.assertLit(mkAtom(3), true, 3, SatLit::positive(3));
    CHECK(s.trailSize() == 3);

    s.backtrackToLevel(1);
    CHECK(s.trailSize() == 1);          // only level-1 entry survives
    CHECK(s.currentLevel() == 1);
    CHECK(s.backtrackCount == 1);
}

TEST_CASE("ArithSolverBase: pending cleared on backtrack when level > target") {
    MockArithSolver s;
    TheoryLemmaDatabase db;

    s.doRecordConflict(3, {SatLit::positive(1)});
    CHECK(s.pending());

    // Backtrack to level 2 (< 3) clears the pending.
    s.backtrackToLevel(2);
    CHECK_FALSE(s.pending());

    // Pending at level 1, backtrack to level 1 keeps it (not > target).
    s.doRecordUnknown(1);
    CHECK(s.pending());
    s.backtrackToLevel(1);
    CHECK(s.pending());
}

TEST_CASE("ArithSolverBase: conflict pending has priority over later non-conflict") {
    MockArithSolver s;
    TheoryLemmaDatabase db;

    s.doRecordConflict(2, {SatLit::positive(7)});
    s.doRecordUnknown(2);   // must NOT overwrite the conflict
    REQUIRE(s.pending());
    auto r = s.check(db);
    CHECK(r.kind == TheoryCheckResult::Kind::Conflict);
}

TEST_CASE("ArithSolverBase: reset wipes trail, pendings, scopes") {
    MockArithSolver s;

    s.assertLit(mkAtom(1), true, 1, SatLit::positive(1));
    s.doRecordConflict(1, {SatLit::positive(1)});
    s.push();
    CHECK(s.scopeLevel() == 1);

    s.reset();
    CHECK(s.trailSize() == 0);
    CHECK_FALSE(s.pending());
    CHECK(s.currentLevel() == 0);
    CHECK(s.scopeLevel() == 0);
    CHECK(s.resetCount == 1);
}

TEST_CASE("ArithSolverBase: push/pop adjust scope and fire hooks") {
    MockArithSolver s;

    s.push();
    s.push();
    CHECK(s.scopeLevel() == 2);
    CHECK(s.pushCount == 2);

    s.pop(1);
    CHECK(s.scopeLevel() == 1);
    CHECK(s.popCount == 1);

    // Over-pop clamps to 0.
    s.pop(5);
    CHECK(s.scopeLevel() == 0);
}
