#include <doctest/doctest.h>
#include "theory/arith/nra/proof/CdcacProof.h"
#include "theory/arith/nra/proof/CdcacProofChecker.h"
#include "theory/arith/nra/fuzz/CdcacFuzzer.h"

using namespace xolver;

TEST_CASE("V7: CdcacProof types are value-based and serializable") {
    CdcacProof proof;
    proof.kind = CdcacProof::Kind::UnsatCovering;

    ProofCovering cov;
    cov.id = 1;
    cov.level = 0;
    cov.var = VarId{0};

    ProofCellCertificate cellCert;
    cellCert.kind = CellCertificateKind::FullLineViolation;
    cellCert.level = 0;
    cellCert.var = VarId{0};

    AtomCondition ac;
    ac.poly = PolyId{1};
    ac.rel = Relation::Gt;
    ac.allowedSigns = makeSignSet({AtomSign::Pos});
    ac.invariantSigns = makeSignSet({AtomSign::Zero});
    cellCert.atomConditions.push_back(ac);

    cov.cells.push_back(cellCert);
    proof.coverings.push_back(cov);

    CHECK(proof.kind == CdcacProof::Kind::UnsatCovering);
    CHECK(proof.coverings.size() == 1);
    CHECK(proof.coverings[0].cells[0].atomConditions.size() == 1);
}

TEST_CASE("V7: ProofCellCertificate uses ProofCoveringId not unique_ptr") {
    ProofCellCertificate cellCert;
    cellCert.childCoverings.push_back(42);
    cellCert.childCoverings.push_back(99);
    CHECK(cellCert.childCoverings[0] == 42);
    CHECK(cellCert.childCoverings[1] == 99);
}

TEST_CASE("V7: CdcacProofChecker accepts SAT proof with model") {
    CdcacProof proof;
    proof.kind = CdcacProof::Kind::SatModel;
    proof.model = SamplePoint{};
    proof.model->varOrder.push_back(VarId{0});
    proof.model->values.push_back(RealAlg::fromRational(mpq_class(0)));

    // Without algebra backend, sign validation returns Unknown
    CdcacProofChecker checker(nullptr);
    auto result = checker.check(proof);
    // Skeleton: returns Valid because there are no sampleSigns to validate
    CHECK(result.status == ProofCheckStatus::Valid);
}

TEST_CASE("V7: CdcacProofChecker rejects SAT proof without model") {
    CdcacProof proof;
    proof.kind = CdcacProof::Kind::SatModel;
    // No model
    CdcacProofChecker checker(nullptr);
    auto result = checker.check(proof);
    CHECK(result.status == ProofCheckStatus::Invalid);
}

TEST_CASE("V7: CdcacProofChecker validates UNSAT covering") {
    CdcacProof proof;
    proof.kind = CdcacProof::Kind::UnsatCovering;

    ProofCovering cov;
    ProofCellCertificate cellCert;
    cellCert.level = 0;
    cellCert.var = VarId{0};
    AtomCondition ac;
    ac.allowedSigns = makeSignSet({AtomSign::Pos});
    ac.invariantSigns = makeSignSet({AtomSign::Zero});
    cellCert.atomConditions.push_back(ac);
    cov.cells.push_back(cellCert);
    cov.coverage.orderedCells.push_back(FiberCellCoverage{});
    proof.coverings.push_back(cov);

    CdcacProofChecker checker(nullptr);
    auto result = checker.check(proof);
    CHECK(result.status == ProofCheckStatus::Valid);
}

TEST_CASE("V7: CdcacProofChecker rejects empty covering") {
    CdcacProof proof;
    proof.kind = CdcacProof::Kind::UnsatCovering;
    ProofCovering cov;
    proof.coverings.push_back(cov);

    CdcacProofChecker checker(nullptr);
    auto result = checker.check(proof);
    CHECK(result.status == ProofCheckStatus::Invalid);
}

TEST_CASE("V7: CdcacProofChecker rejects cell with empty atomConditions") {
    ProofCellCertificate cellCert;
    cellCert.atomConditions.clear();
    CdcacProofChecker checker(nullptr);
    auto result = checker.checkCellCertificate(cellCert);
    CHECK(result.status == ProofCheckStatus::Invalid);
}

TEST_CASE("V7: CdcacFuzzer generates known SAT case") {
    CdcacFuzzer fuzzer(123);
    auto satCase = fuzzer.knownSat(2);
    CHECK(satCase.expectedSat);
    CHECK(satCase.constraints.size() == 4);  // 2 vars * 2 bounds
}

TEST_CASE("V7: CdcacFuzzer generates known UNSAT case") {
    CdcacFuzzer fuzzer(456);
    auto unsatCase = fuzzer.knownUnsat(2);
    CHECK(!unsatCase.expectedSat);
    CHECK(unsatCase.constraints.size() == 4);
}
