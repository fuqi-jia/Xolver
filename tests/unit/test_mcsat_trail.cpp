// Unit tests for the MCSAT M-trail data structure.
//
// These cover the framework-level invariants documented in
// src/experimental/mcsat/MCSatTrail.h: O(1) lookup, LIFO backtrack,
// dedup-on-push, and clear semantics.

#include "experimental/mcsat/MCSatTrail.h"
#include "expr/types.h"
#include "sat/SatSolver.h"
#include "util/RealValue.h"

#include <doctest/doctest.h>

using namespace xolver;
using namespace xolver::mcsat;

TEST_CASE("MCSatTrail: empty after construction") {
    MCSatTrail trail;
    CHECK(trail.empty());
    CHECK(trail.size() == 0);
    CHECK(trail.topLevel() == 0);
    CHECK_FALSE(trail.lookupBool(0).has_value());
    CHECK(trail.lookupVar(0) == nullptr);
}

TEST_CASE("MCSatTrail: push Boolean decision then look up") {
    MCSatTrail trail;
    SatLit lit{7, true};
    REQUIRE(trail.pushBoolDecision(lit, /*level=*/1));
    CHECK(trail.size() == 1);
    CHECK(trail.topLevel() == 1);
    auto v = trail.lookupBool(7);
    REQUIRE(v.has_value());
    CHECK(*v == true);
}

TEST_CASE("MCSatTrail: push theory decision then look up") {
    MCSatTrail trail;
    RealValue val = RealValue::fromInt(42);
    REQUIRE(trail.pushTheoryDecision(/*var=*/5, val, /*level=*/2));
    CHECK(trail.size() == 1);
    const RealValue* got = trail.lookupVar(5);
    REQUIRE(got != nullptr);
    CHECK(*got == RealValue::fromInt(42));
}

TEST_CASE("MCSatTrail: double-push of same atom is rejected") {
    MCSatTrail trail;
    SatLit lit{3, false};
    CHECK(trail.pushBoolPropagation(lit, 1, {lit}));
    CHECK_FALSE(trail.pushBoolPropagation(lit, 2, {lit}));
    CHECK(trail.size() == 1);
}

TEST_CASE("MCSatTrail: double-push of same theory var is rejected") {
    MCSatTrail trail;
    CHECK(trail.pushTheoryDecision(11, RealValue::fromInt(0), 1));
    CHECK_FALSE(trail.pushTheoryDecision(11, RealValue::fromInt(1), 1));
    CHECK(trail.size() == 1);
    CHECK(*trail.lookupVar(11) == RealValue::fromInt(0));
}

TEST_CASE("MCSatTrail: backtrack drops entries strictly above target level") {
    MCSatTrail trail;
    CHECK(trail.pushBoolDecision(SatLit{1, true}, 1));
    CHECK(trail.pushTheoryDecision(101, RealValue::fromInt(7), 2));
    CHECK(trail.pushBoolDecision(SatLit{2, false}, 3));
    REQUIRE(trail.size() == 3);

    trail.backtrackToLevel(1);
    CHECK(trail.size() == 1);
    CHECK_FALSE(trail.lookupBool(2).has_value());
    CHECK(trail.lookupVar(101) == nullptr);
    auto b1 = trail.lookupBool(1);
    REQUIRE(b1.has_value());
    CHECK(*b1 == true);
}

TEST_CASE("MCSatTrail: backtrack to 0 leaves trail empty") {
    MCSatTrail trail;
    CHECK(trail.pushBoolDecision(SatLit{1, true}, 1));
    CHECK(trail.pushTheoryDecision(101, RealValue::fromInt(7), 2));
    trail.backtrackToLevel(0);
    CHECK(trail.empty());
    CHECK_FALSE(trail.lookupBool(1).has_value());
    CHECK(trail.lookupVar(101) == nullptr);
}

TEST_CASE("MCSatTrail: clear empties trail and indices") {
    MCSatTrail trail;
    trail.pushBoolDecision(SatLit{9, true}, 1);
    trail.pushTheoryDecision(33, RealValue::fromInt(2), 2);
    trail.clear();
    CHECK(trail.empty());
    CHECK(trail.lookupVar(33) == nullptr);
    CHECK_FALSE(trail.lookupBool(9).has_value());
}

TEST_CASE("MCSatTrail: reasoned propagation roundtrip") {
    MCSatTrail trail;
    std::vector<SatLit> reasons = {SatLit{1, true}, SatLit{2, false}};
    REQUIRE(trail.pushTheoryPropagation(50, RealValue::fromInt(0), 3, reasons));
    REQUIRE(trail.size() == 1);
    const auto& entry = trail.entries().front();
    CHECK(entry.kind == TrailEntryKind::TheoryPropagation);
    CHECK(entry.reasonLits.size() == 2);
    CHECK(entry.reasonLits[0] == SatLit{1, true});
    CHECK(entry.reasonLits[1] == SatLit{2, false});
}

TEST_CASE("MCSatTrail: NullVar theory push is rejected") {
    MCSatTrail trail;
    CHECK_FALSE(trail.pushTheoryDecision(NullVar, RealValue::fromInt(0), 1));
    CHECK(trail.empty());
}
