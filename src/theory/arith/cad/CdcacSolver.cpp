#include "theory/arith/cad/CdcacSolver.h"

namespace nlcolver {

CdcacSolver::CdcacSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)) {}

void CdcacSolver::push() {}
void CdcacSolver::pop(uint32_t) {}

void CdcacSolver::reset() {
    constraints_.clear();
    trail_.clear();
    allVars_.clear();
}

void CdcacSolver::collectVars(const std::vector<std::pair<std::string, mpq_class>>& coeffs) {
    for (const auto& [name, coeff] : coeffs) {
        (void)coeff;
        allVars_.insert(name);
    }
}

void CdcacSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit /*reason*/) {
    if (!std::holds_alternative<PolynomialAtomPayload>(atom.payload)) {
        // Unsupported payload: NRA solver can only handle polynomial atoms.
        return;
    }
    const auto& payload = std::get<PolynomialAtomPayload>(atom.payload);

    Relation effectiveRel = value ? payload.rel : negateRelation(payload.rel);

    // If effective relation is unsupported, ignore (check will return Unknown).
    (void)effectiveRel;

    // TODO: integrate with polynomial kernel once polynomial extraction is available.
    // For now, accumulate constraints for future use.
    constraints_.push_back({atom.satVar, payload.poly, effectiveRel});
    trail_.push_back({level, constraints_.size()});
}

void CdcacSolver::backtrackToLevel(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        constraints_.resize(trail_.back().constraintsSize);
        trail_.pop_back();
    }
}

TheoryCheckResult CdcacSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    // NRA solver is not fully migrated to the new trail-based interface yet.
    // Return Unknown to maintain soundness.
    return TheoryCheckResult::unknown();
}

} // namespace nlcolver
