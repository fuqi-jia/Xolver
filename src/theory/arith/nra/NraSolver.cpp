#include "theory/arith/nra/NraSolver.h"
#include "theory/arith/linear/LinearExpr.h"

namespace nlcolver {

NraSolver::NraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      engine_(kernel_.get()) {}

void NraSolver::push() {}
void NraSolver::pop(uint32_t) {}

void NraSolver::reset() {
    engine_.reset();
    activeLits_.clear();
    trail_.clear();
    activeSet_.reset();
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    // Facade-level dedup: same polarity already active → ignore.
    // Opposite polarity is left to the engine's defense-in-depth check.
    if (activeSet_.contains(reason)) {
        return;
    }
    activeSet_.insert(reason);

    size_t oldSize = activeLits_.size();
    activeLits_.push_back(reason);
    trail_.push_back({level, oldSize});

    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        // Payload mismatch is an internal routing error, NOT a theory conflict.
        // Engine will see this as unsupported and return Unknown.
        engine_.reset();
        return;
    }

    Relation rel = value ? payload->rel : negateRelation(payload->rel);
    engine_.assertConstraint(payload->poly, rel, reason, level);
}

void NraSolver::backtrackToLevel(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        activeLits_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    activeSet_.rebuildFromActive(activeLits_, [](const auto& lit) { return lit; });
    engine_.backtrack(level);
}

TheoryCheckResult NraSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    return engine_.check();
}

} // namespace nlcolver
