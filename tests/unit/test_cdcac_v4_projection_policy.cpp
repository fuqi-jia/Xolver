#include <doctest/doctest.h>
#include "theory/arith/nra/CdcacTypes.h"
#include "theory/arith/nra/ProjectionPolicy.h"
#include "theory/arith/nra/EquationalConstraintManager.h"
#include "theory/arith/nra/NullificationAnalyzer.h"

using namespace nlcolver;

TEST_CASE("V4: CollinsConservativePolicy produces non-degenerate result for empty input") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    CollinsConservativePolicy policy;
    auto result = policy.project(input, ctx);

    CHECK(result.kind == ProjectionPolicyKind::CollinsConservative);
    CHECK(!result.hasDegeneracy);
    CHECK(result.projectionPolys.empty());
    CHECK(result.obligations.empty());
    CHECK(!result.isReduced);
}

TEST_CASE("V4: McCallumReducedPolicy falls back on degeneracy") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    McCallumReducedPolicy policy;
    auto result = policy.project(input, ctx);

    CHECK(result.kind == ProjectionPolicyKind::McCallumReduced);
    CHECK(!result.isReduced);  // V4 skeleton: not truly reduced yet
}

TEST_CASE("V4: LazardStylePolicy skeleton") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    LazardStylePolicy policy;
    auto result = policy.project(input, ctx);

    CHECK(result.kind == ProjectionPolicyKind::LazardStyle);
}

TEST_CASE("V4: ECReducedPolicy skeleton") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    ECReducedPolicy policy;
    auto result = policy.project(input, ctx);

    CHECK(result.kind == ProjectionPolicyKind::ECReduced);
}

TEST_CASE("V4: HybridAdaptivePolicy fallback to conservative") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    HybridAdaptivePolicy policy;
    auto result = policy.project(input, ctx);

    CHECK(result.kind == ProjectionPolicyKind::HybridAdaptive);
}

TEST_CASE("V4: validateObligations returns Valid for conservative") {
    ProjectionInput input;
    input.eliminateVar = VarId{0};
    ProjectionContext ctx;

    CollinsConservativePolicy policy;
    auto result = policy.project(input, ctx);

    // Conservative projection has no obligations; algebra can be nullptr.
    auto validation = policy.validateObligations(result, Cell{}, nullptr);
    CHECK(validation.status == ValidationStatus::Valid);
}

TEST_CASE("V4: EquationalConstraintManager detects EQ constraints") {
    EquationalConstraintManager mgr(nullptr);

    ActiveConstraintSet active;
    CdcacConstraint c1;
    c1.id = ConstraintId{1};
    c1.poly = PolyId{1};
    c1.rel = Relation::Eq;
    c1.reason = SatLit{1, true};
    active.constraints.push_back(c1);

    CdcacConstraint c2;
    c2.id = ConstraintId{2};
    c2.poly = PolyId{2};
    c2.rel = Relation::Gt;  // not an EC
    c2.reason = SatLit{2, true};
    active.constraints.push_back(c2);

    auto ecs = mgr.detectActiveECs(active);
    CHECK(ecs.size() == 1);
    CHECK(ecs[0].normalized.rel == Relation::Eq);
}

TEST_CASE("V4: EquationalConstraintManager choosePolicy returns conservative when no ECs") {
    EquationalConstraintManager mgr(nullptr);
    auto policy = mgr.choosePolicy({});
    CHECK(policy != nullptr);
    CHECK(policy->kind() == ProjectionPolicyKind::CollinsConservative);
}

TEST_CASE("V4: NullificationAnalyzer V4 repair skeleton") {
    NullificationAnalyzer na(nullptr);

    // analyzeProjectionPoly is a skeleton in V4
    ReasonedPolynomial rp;
    SamplePoint prefix;
    auto analysis = na.analyzeProjectionPoly(rp, prefix, VarId{0});
    CHECK(analysis.action == NullificationAnalyzer::Action::ContinueNormally);
}

TEST_CASE("V4: NullificationRepair type exists and has expected fields") {
    NullificationRepair repair;
    CHECK(repair.kind == NullificationRepairKind::Unknown);
    CHECK(repair.replacementPolys.empty());
    CHECK(repair.newObligations.empty());
    CHECK(!repair.immediateConflict.has_value());
}

TEST_CASE("V4: DelineabilityCondition type exists and has expected fields") {
    DelineabilityCondition dc;
    CHECK(dc.poly == NullPoly);
    CHECK(dc.mainVar == NullVar);
    CHECK(dc.leadingCoeffNonzero.empty());
    CHECK(dc.discriminantNonzero.empty());
    CHECK(dc.resultantNonzero.empty());
    CHECK(dc.obligations.empty());
}

TEST_CASE("V4: PolicyProjectionResult type exists with fallback support") {
    PolicyProjectionResult result;
    CHECK(result.kind == ProjectionPolicyKind::CollinsConservative);
    CHECK(!result.isReduced);
    CHECK(!result.fallbackCondition.has_value());
    CHECK(!result.hasDegeneracy);
}
