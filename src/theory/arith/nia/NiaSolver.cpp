#include "theory/arith/nia/NiaSolver.h"
#include "theory/arith/linear/LinearExpr.h"
#include <unordered_set>

namespace nlcolver {

NiaSolver::NiaSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)),
      normalizer_(*kernel_),
      validator_(*kernel_),
      univariate_(*kernel_),
      linearDomain_(*kernel_),
      algebraic_(*kernel_),
      bounded_(*kernel_),
      localSearch_(*kernel_) {}

void NiaSolver::push() {}
void NiaSolver::pop(uint32_t) {}

void NiaSolver::reset() {
    active_.clear();
    trail_.clear();
    pendingConflict_.reset();
    pendingUnknown_.reset();
    currentModel_.reset();
}

void NiaSolver::assertLit(const TheoryAtomRecord& atom, bool value,
                          int level, SatLit reason) {
    const auto* payload = std::get_if<PolynomialAtomPayload>(&atom.payload);
    if (!payload) {
        pendingUnknown_ = PendingUnknown{level};
        return;
    }

    size_t oldSize = active_.size();
    Relation rel = value ? payload->rel : negateRelation(payload->rel);

    // Normalize (poly - rhs) rel 0 form
    PolyId diff = payload->poly;
    if (payload->rhs != 0) {
        PolyId rhsPoly = kernel_->mkConst(payload->rhs);
        diff = kernel_->sub(payload->poly, rhsPoly);
    }

    active_.push_back({diff, rel, reason});
    trail_.push_back({level, oldSize});
}

void NiaSolver::backtrackToLevel(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        active_.resize(trail_.back().activeSizeBefore);
        trail_.pop_back();
    }
    if (pendingConflict_ && pendingConflict_->level > level) {
        pendingConflict_.reset();
    }
    if (pendingUnknown_ && pendingUnknown_->level > level) {
        pendingUnknown_.reset();
    }
}

static std::unordered_set<std::string> collectVars(
    const std::vector<NormalizedNiaConstraint>& constraints,
    PolynomialKernel& kernel) {
    std::unordered_set<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel.variables(c.poly)) {
            vars.insert(v);
        }
    }
    return vars;
}

TheoryCheckResult NiaSolver::check(TheoryLemmaDatabase& lemmaDb) {
    if (pendingUnknown_) return TheoryCheckResult::unknown();
    if (pendingConflict_) return TheoryCheckResult::mkConflict(pendingConflict_->conflict);
    if (active_.empty()) return TheoryCheckResult::consistent();

    // 1. Normalize
    auto normalizedOpt = normalizer_.normalize(active_);
    if (!normalizedOpt) return TheoryCheckResult::unknown();
    const auto& normalized = *normalizedOpt;

    // 2. Trivial constants
    std::vector<SatLit> conflictLits;
    bool hasNonConstant = false;
    for (const auto& c : normalized) {
        if (!kernel_->isConstant(c.poly)) {
            hasNonConstant = true;
            continue;
        }
        mpq_class val = kernel_->toConstant(c.poly);
        if (!relationSatisfied(val, c.rel)) {
            conflictLits.push_back(c.reason.negated());
        }
    }
    if (!conflictLits.empty()) {
        return TheoryCheckResult::mkConflict(TheoryConflict{conflictLits});
    }
    if (!hasNonConstant) {
        return TheoryCheckResult::consistent();
    }

    // 3. Reset domains
    domains_.reset();

    // 4. Linear domain inference
    auto lr = linearDomain_.run(normalized, domains_);
    if (lr.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*lr.conflict);
    }
    if (lr.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown();
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }

    // 5. Univariate reasoning
    auto ur = univariate_.run(normalized, domains_, lemmaDb);
    if (ur.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ur.conflict);
    }
    if (ur.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ur.lemma);
    }
    if (ur.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown();
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }

    // 6. Algebraic reasoning
    auto ar = algebraic_.run(normalized, domains_, lemmaDb);
    if (ar.kind == NiaReasoningKind::Conflict) {
        return TheoryCheckResult::mkConflict(*ar.conflict);
    }
    if (ar.kind == NiaReasoningKind::Lemma) {
        return TheoryCheckResult::mkLemma(*ar.lemma);
    }
    if (ar.kind == NiaReasoningKind::FatalUnknown) {
        return TheoryCheckResult::unknown();
    }
    if (domains_.isEmpty()) {
        return TheoryCheckResult::mkConflict(domains_.buildEmptyDomainConflict());
    }

    // 7. Bounded complete solver
    auto allVars = collectVars(normalized, *kernel_);
    if (domains_.allFinite(allVars)) {
        auto br = bounded_.solve(normalized, domains_, validator_, lemmaDb);
        if (br.status == BoundedSolveStatus::Sat) {
            currentModel_ = br.model;
            return TheoryCheckResult::consistent();
        }
        if (br.status == BoundedSolveStatus::UnsatComplete) {
            return TheoryCheckResult::mkConflict(*br.conflict);
        }
        // UnknownBudget / UnknownUnsupported: continue pipeline
    }

    // 8. Local search SAT finder
    if (auto model = localSearch_.tryFindModel(normalized, domains_)) {
        if (validator_.validate(*model, normalized)) {
            currentModel_ = *model;
            return TheoryCheckResult::consistent();
        }
    }

    // 9. Branch split or Unknown
    if (auto lemma = buildBranchLemma(normalized, domains_, lemmaDb)) {
        return TheoryCheckResult::mkLemma(*lemma);
    }

    return TheoryCheckResult::unknown();
}

bool NiaSolver::relationSatisfied(const mpq_class& val, Relation rel) const {
    switch (rel) {
        case Relation::Eq:  return val == 0;
        case Relation::Neq: return val != 0;
        case Relation::Lt:  return val <  0;
        case Relation::Leq: return val <= 0;
        case Relation::Gt:  return val >  0;
        case Relation::Geq: return val >= 0;
    }
    return false;
}

std::optional<TheoryLemma> NiaSolver::buildBranchLemma(
    const std::vector<NormalizedNiaConstraint>& /*constraints*/,
    const DomainStore& /*domains*/,
    TheoryLemmaDatabase& /*lemmaDb*/) {

    // Phase NIA-Core: branch lemma generation is a skeleton.
    // Globally valid integer splits: x <= k ∨ x >= k+1
    return std::nullopt;
}

} // namespace nlcolver
