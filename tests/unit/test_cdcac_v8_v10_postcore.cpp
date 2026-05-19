#include <doctest/doctest.h>
#include "theory/arith/nra/core/CdcacObjective.h"

using namespace nlcolver;

TEST_CASE("V8: BooleanAwareConflict type exists") {
    BooleanAwareConflict bac;
    bac.coreReasons.push_back(SatLit{1, true});
    bac.booleanAtoms.push_back(AtomId{2});
    CHECK(bac.coreReasons.size() == 1);
    CHECK(bac.booleanAtoms.size() == 1);
    CHECK(!bac.coveringCert.has_value());
}

TEST_CASE("V9: OptResultKind enum values") {
    CHECK(static_cast<int>(OptResultKind::AttainedOptimum) == 0);
    CHECK(static_cast<int>(OptResultKind::NonAttainedInfimum) == 1);
    CHECK(static_cast<int>(OptResultKind::Unbounded) == 2);
    CHECK(static_cast<int>(OptResultKind::Unknown) == 3);
}

TEST_CASE("V9: ObjectiveCertificate default state") {
    ObjectiveCertificate cert;
    CHECK(cert.kind == OptResultKind::Unknown);
    CHECK(!cert.optimizer.has_value());
    CHECK(!cert.infimum.has_value());
    CHECK(!cert.betterThanBoundUnsatProof.has_value());
    CHECK(cert.boundaryCertificates.empty());
}

TEST_CASE("V9: ObjectiveCellCertificate with boundary value") {
    ObjectiveCellCertificate occ;
    occ.localKind = OptResultKind::AttainedOptimum;
    occ.boundaryValue = RealAlg::fromRational(mpq_class(42));
    CHECK(occ.localKind == OptResultKind::AttainedOptimum);
    CHECK(occ.boundaryValue.has_value());
    CHECK(occ.boundaryValue->isRational());
    CHECK(occ.boundaryValue->rational == mpq_class(42));
}

TEST_CASE("V9: Objective minimize/maximize") {
    Objective obj;
    obj.poly = PolyId{1};
    obj.minimize = true;
    CHECK(obj.minimize);
    obj.minimize = false;
    CHECK(!obj.minimize);
}

TEST_CASE("V10: TranscendentalConstraint type exists") {
    TranscendentalConstraint tc;
    tc.kind = TranscendentalKind::Sin;
    tc.argPoly = PolyId{1};
    tc.rel = Relation::Eq;
    tc.rhs = mpq_class(0);
    CHECK(tc.kind == TranscendentalKind::Sin);
}

TEST_CASE("V10: All TranscendentalKind values") {
    CHECK(static_cast<int>(TranscendentalKind::Sin) == 0);
    CHECK(static_cast<int>(TranscendentalKind::Cos) == 1);
    CHECK(static_cast<int>(TranscendentalKind::Exp) == 2);
    CHECK(static_cast<int>(TranscendentalKind::Log) == 3);
    CHECK(static_cast<int>(TranscendentalKind::Pow) == 4);
}
