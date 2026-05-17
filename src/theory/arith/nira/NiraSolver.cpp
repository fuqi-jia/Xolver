#include "theory/arith/nira/NiraSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearAtomManager.h"
#include <iostream>
#include <algorithm>

namespace nlcolver {

NiraSolver::NiraSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)) {
    if (kernel_) {
        converter_ = std::make_unique<PolynomialConverter>(*kernel_);
    }
}

NiraSolver::~NiraSolver() = default;

void NiraSolver::push() {
    gsRelax_.push();
}

void NiraSolver::pop(uint32_t n) {
    for (uint32_t i = 0; i < n; ++i) {
        gsRelax_.pop();
    }
}

void NiraSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void NiraSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
    gsRelax_.backtrackToLevel(level);
}

TheoryCheckResult NiraSolver::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort effort) {
    (void)effort;
    if (activeAssignments_.empty()) {
        return TheoryCheckResult::consistent();
    }

    // --- Presolve: fixed-value substitution ---
    if (kernel_) {
        std::unordered_map<std::string, mpq_class> fixedValues;

        // Step 1: collect fixed values from linear equalities
        for (const auto& a : activeAssignments_) {
            if (!std::holds_alternative<LinearAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<LinearAtomPayload>(a.atom.payload);
            if (payload.rel != Relation::Eq) continue;
            if (payload.lhs.terms.size() != 1) continue;

            const auto& term = payload.lhs.terms[0];
            if (term.second == 0) continue;
            fixedValues[term.first] = payload.rhs / term.second;
        }

        // Step 2: substitute into polynomial constraints
        for (const auto& a : activeAssignments_) {
            if (!std::holds_alternative<PolynomialAtomPayload>(a.atom.payload)) continue;
            if (!a.value) continue;

            const auto& payload = std::get<PolynomialAtomPayload>(a.atom.payload);
            PolyId current = payload.poly;

            for (const auto& [name, value] : fixedValues) {
                auto varIdOpt = kernel_->findVar(name);
                if (!varIdOpt) {
                    continue;
                }
                auto substituted = kernel_->substituteRational(current, *varIdOpt, value);
                if (substituted) {
                    current = *substituted;
                }
            }

            if (kernel_->isConstant(current)) {
                mpq_class val = kernel_->toConstant(current);
                bool satisfied = false;
                switch (payload.rel) {
                    case Relation::Eq:  satisfied = (val == 0); break;
                    case Relation::Neq: satisfied = (val != 0); break;
                    case Relation::Lt:  satisfied = (val < 0); break;
                    case Relation::Leq: satisfied = (val <= 0); break;
                    case Relation::Gt:  satisfied = (val > 0); break;
                    case Relation::Geq: satisfied = (val >= 0); break;
                }
                if (!satisfied) {
                    return TheoryCheckResult::mkConflict(TheoryConflict{{a.lit}});
                }
            }
        }
    }

    // TODO: classify, pure subproblem delegation, relaxation, bounded-complete
    return TheoryCheckResult::unknown();
}

TheoryCheckResult NiraSolver::checkPureSubproblems(TheoryLemmaDatabase& /*lemmaDb*/) {
    return TheoryCheckResult::consistent();
}

TheoryCheckResult NiraSolver::checkRelaxationAndValidate(TheoryLemmaDatabase& /*lemmaDb*/) {
    return TheoryCheckResult::unknown();
}

TheoryCheckResult NiraSolver::checkBoundedComplete(TheoryLemmaDatabase& /*lemmaDb*/) {
    return TheoryCheckResult::unknown();
}

bool NiraSolver::validateOriginalConstraints() const {
    return true;
}

void NiraSolver::reset() {
    activeAssignments_.clear();
    gsRelax_.reset();
}

void NiraSolver::setRegistry(TheoryAtomRegistry* reg) {
    registry_ = reg;
}

std::optional<TheorySolver::TheoryModel> NiraSolver::getModel() const {
    return std::nullopt;
}

std::vector<SatLit> NiraSolver::allActiveReasons() const {
    std::vector<SatLit> reasons;
    for (const auto& a : activeAssignments_) {
        reasons.push_back(a.lit);
    }
    return reasons;
}

} // namespace nlcolver
