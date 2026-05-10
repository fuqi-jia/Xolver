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
}

void NraSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
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
    engine_.backtrack(level);
}

TheoryCheckResult NraSolver::check(TheoryLemmaDatabase& /*lemmaDb*/) {
    return engine_.check();
}

} // namespace nlcolver
