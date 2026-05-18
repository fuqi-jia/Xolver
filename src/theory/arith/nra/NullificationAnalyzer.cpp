#include "theory/arith/nra/NullificationAnalyzer.h"
#include "theory/arith/nra/AlgebraBackend.h"

namespace nlcolver {

NullificationAnalyzer::NullificationAnalyzer(AlgebraBackend* algebra)
    : algebra_(algebra) {}

NullificationAnalyzer::Analysis NullificationAnalyzer::analyzeConstraint(
    const CdcacConstraint& c,
    const SamplePoint& prefix,
    VarId currentVar) {

    Analysis analysis;

    if (!algebra_) {
        analysis.reason = CdcacUnknownReason::BackendFailure;
        return analysis;
    }

    auto vanish = algebra_->vanishesAtPrefix(c.poly, prefix, currentVar);

    if (vanish == VanishResult::Unknown) {
        analysis.action = Action::Unknown;
        analysis.reason = CdcacUnknownReason::NullificationUnresolved;
        return analysis;
    }

    if (vanish == VanishResult::NonVanishes) {
        analysis.action = Action::ContinueNormally;
        return analysis;
    }

    // Polynomial vanishes at prefix
    switch (c.rel) {
        case Relation::Eq:
            // 0 = 0 is always true → skip constraint
            analysis.action = Action::SkipConstraintAsTrue;
            analysis.repair.kind = NullificationRepairKind::ConstraintDropped;
            return analysis;

        case Relation::Neq:
        case Relation::Lt:
        case Relation::Leq:
        case Relation::Gt:
        case Relation::Geq:
            // 0 ≠ 0, 0 < 0, etc. are always false → FullLine conflict
            analysis.action = Action::ReturnFullLineConflict;
            {
                Cell cell;
                cell.var = currentVar;
                cell.kind = CellKind::FullLine;
                cell.lower = Bound::negInf();
                cell.upper = Bound::posInf();
                cell.reasons = {c.reason};
                analysis.conflictCell = std::move(cell);

                // V4: build certified immediate conflict
                analysis.repair.kind = NullificationRepairKind::ImmediateConflict;
                analysis.repair.reason = CdcacUnknownReason::None;
            }
            return analysis;
    }

    analysis.action = Action::Unknown;
    analysis.reason = CdcacUnknownReason::InternalInvariantViolation;
    return analysis;
}

NullificationAnalyzer::Analysis NullificationAnalyzer::analyzeProjectionPoly(
    const ReasonedPolynomial& /*rp*/,
    const SamplePoint& /*prefix*/,
    VarId /*currentVar*/) {

    // V4 skeleton: projection nullification analysis is not yet fully wired.
    // Full implementation requires PolynomialKernel access for toPolyId and
    // obligation generation for each nullified projection polynomial.
    Analysis analysis;
    analysis.action = Action::ContinueNormally;
    analysis.repair.kind = NullificationRepairKind::NoRepairNeeded;
    return analysis;
}

NullificationRepair NullificationAnalyzer::attemptRepair(
    const ReasonedPolynomial& /*rp*/,
    const SamplePoint& /*prefix*/,
    VarId /*currentVar*/) {

    // V4 skeleton: full repair with obligations requires:
    // 1. Detect which coefficient/subresultant caused nullification
    // 2. Generate ProjectionObligation for non-vanishing witness
    // 3. Build CertifiedCell if immediate conflict
    // For now, return Unknown.
    NullificationRepair repair;
    repair.kind = NullificationRepairKind::Unknown;
    repair.reason = CdcacUnknownReason::NullificationUnresolved;
    return repair;
}

} // namespace nlcolver
