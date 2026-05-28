#include <doctest/doctest.h>
#include "theory/arith/nra/core/CdcacCache.h"
#include "theory/arith/nra/preprocess/ActiveConstraintSet.h"

using namespace xolver;

TEST_CASE("V5: CdcacCache sign cache get/set") {
    CdcacCache cache;
    SignCacheKey key;
    key.poly = PolyId{1};
    key.varOrder = {VarId{0}};
    key.policy = ProjectionPolicyKind::CollinsConservative;

    CHECK(!cache.getSign(key).has_value());
    cache.setSign(key, Sign::Pos);
    auto val = cache.getSign(key);
    CHECK(val.has_value());
    CHECK(*val == Sign::Pos);
}

TEST_CASE("V5: CdcacCache root cache get/set") {
    CdcacCache cache;
    SamplePoint prefix;
    prefix.push(VarId{0}, RealAlg::fromRational(mpq_class(0)));

    CHECK(!cache.getRoots(PolyId{1}, prefix, VarId{0}).has_value());
    RootSet rs;
    rs.roots.push_back(RealAlg::fromRational(mpq_class(1)));
    cache.setRoots(PolyId{1}, prefix, VarId{0}, rs);
    auto val = cache.getRoots(PolyId{1}, prefix, VarId{0});
    CHECK(val.has_value());
    CHECK(val->numRoots() == 1);
}

TEST_CASE("V5: CdcacCache clear empties all caches") {
    CdcacCache cache;
    SignCacheKey key;
    key.poly = PolyId{1};
    cache.setSign(key, Sign::Neg);
    CHECK(cache.totalEntries() > 0);
    cache.clear();
    CHECK(cache.totalEntries() == 0);
}

TEST_CASE("V5: CdcacCache push/pop clears cache (skeleton)") {
    CdcacCache cache;
    SignCacheKey key;
    key.poly = PolyId{1};
    cache.setSign(key, Sign::Pos);
    CHECK(cache.totalEntries() == 1);
    cache.push();
    // Skeleton: push clears cache for soundness
    CHECK(cache.totalEntries() == 0);
    cache.setSign(key, Sign::Neg);
    CHECK(cache.totalEntries() == 1);
    cache.pop(1);
    // Skeleton: pop clears cache for soundness
    CHECK(cache.totalEntries() == 0);
}

TEST_CASE("V5: ActiveConstraintSet add and find") {
    ActiveConstraintSet set;
    ActiveConstraintEntry e1;
    e1.id = ConstraintId{1};
    e1.poly = PolyId{10};
    e1.rel = Relation::Eq;
    e1.reason = SatLit{1, true};
    e1.level = 0;
    set.addConstraint(e1);

    CHECK(set.size() == 1);
    auto found = set.find(ConstraintId{1});
    CHECK(found != nullptr);
    CHECK(found->poly == PolyId{10});

    auto notFound = set.find(ConstraintId{99});
    CHECK(notFound == nullptr);

    auto byLit = set.findByLit(SatLit{1, true});
    CHECK(byLit != nullptr);
    CHECK(byLit->poly == PolyId{10});
}

TEST_CASE("V5: ActiveConstraintSet push/pop") {
    ActiveConstraintSet set;
    set.push();

    ActiveConstraintEntry e1;
    e1.id = ConstraintId{1};
    e1.poly = PolyId{10};
    e1.reason = SatLit{1, true};
    set.addConstraint(e1);
    CHECK(set.size() == 1);

    set.push();
    ActiveConstraintEntry e2;
    e2.id = ConstraintId{2};
    e2.poly = PolyId{20};
    e2.reason = SatLit{2, true};
    set.addConstraint(e2);
    CHECK(set.size() == 2);

    set.pop(1);
    CHECK(set.size() == 1);
    CHECK(set.find(ConstraintId{1}) != nullptr);
    CHECK(set.find(ConstraintId{2}) == nullptr);

    set.pop(1);
    CHECK(set.empty());
}

TEST_CASE("V5: ActiveConstraintSet activePolys deduplicates") {
    ActiveConstraintSet set;
    ActiveConstraintEntry e1;
    e1.poly = PolyId{5};
    set.addConstraint(e1);
    ActiveConstraintEntry e2;
    e2.poly = PolyId{5};
    set.addConstraint(e2);
    ActiveConstraintEntry e3;
    e3.poly = PolyId{7};
    set.addConstraint(e3);

    auto polys = set.activePolys();
    CHECK(polys.size() == 2);
}

TEST_CASE("V5: ActiveConstraintSet equationalConstraints") {
    ActiveConstraintSet set;
    ActiveConstraintEntry e1;
    e1.poly = PolyId{1};
    e1.rel = Relation::Eq;
    e1.isEC = true;
    set.addConstraint(e1);
    ActiveConstraintEntry e2;
    e2.poly = PolyId{2};
    e2.rel = Relation::Eq;
    e2.isEC = false;
    set.addConstraint(e2);
    ActiveConstraintEntry e3;
    e3.poly = PolyId{3};
    e3.rel = Relation::Gt;
    set.addConstraint(e3);

    auto ecs = set.equationalConstraints();
    CHECK(ecs.size() == 1);
    CHECK(ecs[0].poly == PolyId{1});
}

TEST_CASE("V5: ActiveConstraintSet removeConstraintsAboveLevel") {
    ActiveConstraintSet set;
    ActiveConstraintEntry e1;
    e1.id = ConstraintId{1};
    e1.level = 0;
    set.addConstraint(e1);
    ActiveConstraintEntry e2;
    e2.id = ConstraintId{2};
    e2.level = 2;
    set.addConstraint(e2);
    ActiveConstraintEntry e3;
    e3.id = ConstraintId{3};
    e3.level = 5;
    set.addConstraint(e3);

    set.removeConstraintsAboveLevel(2);
    CHECK(set.size() == 2);
    CHECK(set.find(ConstraintId{1}) != nullptr);
    CHECK(set.find(ConstraintId{2}) != nullptr);
    CHECK(set.find(ConstraintId{3}) == nullptr);
}
