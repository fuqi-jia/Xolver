#include "search/linear/LinearPredicatePropagation.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "contracts/TheoryAssignmentView.h"
#include "contracts/TheoryPropagatorCallbacks.h"
#include <algorithm>
#include <utility>

namespace xolver {
namespace {
Relation reverseRelation(Relation relation) {
    switch (relation) {
        case Relation::Lt: return Relation::Gt;
        case Relation::Leq: return Relation::Geq;
        case Relation::Gt: return Relation::Lt;
        case Relation::Geq: return Relation::Leq;
        default: return relation;
    }
}
}

void LinearPredicatePropagation::reset() {
    trail_.clear();
    seenRecords_ = 0;
    familyIndex_.clear();
    families_.clear();
    atoms_.clear();
    dirty_.clear();
    pending_.clear();
}

void LinearPredicatePropagation::markDirty(size_t family) {
    auto& entry = families_[family];
    if (entry.atoms.size() < 2 || entry.dirty) return;
    entry.dirty = true;
    dirty_.push_back(family);
}

void LinearPredicatePropagation::synchronize(const TheoryAtomRegistry& registry) {
    const auto& records = registry.records();
    if (seenRecords_ > records.size()) reset();
    while (seenRecords_ < records.size()) {
        const auto version = seenRecords_++;
        const auto& record = records[version];
        if (!std::holds_alternative<LinearAtomPayload>(record.payload)) continue;
        const auto& payload = std::get<LinearAtomPayload>(record.payload);
        if (!payload.rhs.isRational() || payload.lhs.terms.empty()) continue;
        auto form = payload.lhs;
        auto relation = payload.rel;
        mpq_class endpoint = payload.rhs.asRational();
        if (form.terms.front().second < 0) {
            for (auto& term : form.terms) term.second = -term.second;
            endpoint = -endpoint;
            relation = reverseRelation(relation);
        }
        const auto [position, inserted] = familyIndex_[record.theory].try_emplace(form, families_.size());
        if (inserted) families_.push_back({});
        const size_t family = position->second;
        auto previous = atoms_.find(record.satVar);
        if (previous != atoms_.end()) {
            const auto& old = previous->second;
            if (old.family == family && old.relation == relation && old.endpoint == endpoint) continue;
            markDirty(old.family);
            auto& members = families_[old.family].atoms;
            members.erase(std::remove(members.begin(), members.end(), record.satVar), members.end());
            pending_.clear();
        }
        atoms_.insert_or_assign(record.satVar, Atom{family, relation, std::move(endpoint), version});
        families_[family].atoms.push_back(record.satVar);
        // A new predicate can be implied by sources asserted before it existed.
        if (!trail_.empty()) markDirty(family);
    }
}

void LinearPredicatePropagation::assertLit(const TheoryAtomRegistry& registry,
    const TheoryAtomRecord& atom, SatLit literal, int level) {
    const auto* payload = std::get_if<LinearAtomPayload>(&atom.payload);
    if (!payload || literal.var != atom.satVar) return;
    const auto* registered = registry.findBySatVar(atom.satVar);
    if (!registered) return;
    if (registered != &atom) {
        const auto* declared = std::get_if<LinearAtomPayload>(&registered->payload);
        if (!declared || registered->theory != atom.theory || declared->lhs != payload->lhs ||
            declared->rel != payload->rel || !declared->rhs.isRational() || !payload->rhs.isRational() ||
            declared->rhs.asRational() != payload->rhs.asRational()) return;
    }
    synchronize(registry);
    const auto found = atoms_.find(atom.satVar);
    if (found == atoms_.end()) return;
    const auto& metadata = found->second;
    Assertion entry{literal, level, metadata.family, metadata.version};
    if (const auto position = trail_.find(literal.var)) {
        const auto& old = trail_[*position];
        if (old.literal == literal && old.level == level && old.version == entry.version) return;
        markDirty(old.family);
        trail_.replace(*position, entry);
    } else {
        trail_.append(entry);
    }
    markDirty(entry.family);
}

void LinearPredicatePropagation::backtrackToLevel(int level) {
    const auto withdrawn = trail_.backtrack(level,
        [&](const Assertion& entry) { markDirty(entry.family); });
    if (withdrawn.kind == Trail::Withdrawal::Filtered)
        for (size_t family = 0; family < families_.size(); ++family) markDirty(family);
    // Pending facts are valid clauses, but their premises may cease to be active.
    // Revisit their families instead of installing irrelevant old-branch facts.
    for (const auto& inference : pending_) for (const auto literal : inference.reasons) {
        const auto found = atoms_.find(literal.var);
        if (found != atoms_.end()) markDirty(found->second.family);
    }
    pending_.clear();
}

std::optional<bool> LinearPredicatePropagation::value(SatVar variable,
    const TheoryAssignmentView* assignment) const {
    if (assignment) {
        const auto result = assignment->value(SatLit::positive(variable));
        if (result == LitValue::Unknown) return std::nullopt;
        return result == LitValue::True;
    }
    const auto position = trail_.find(variable);
    if (!position) return std::nullopt;
    const auto& entry = trail_[*position];
    const auto found = atoms_.find(variable);
    if (found == atoms_.end() || found->second.version != entry.version) return std::nullopt;
    return entry.literal.sign;
}

void LinearPredicatePropagation::derive(size_t family, const TheoryAssignmentView* assignment) {
    struct Endpoint { const mpq_class* point; bool strict; SatLit reason; };
    struct Excluded { const mpq_class* point; SatLit reason; };
    std::optional<Endpoint> lower, upper;
    std::vector<Excluded> excluded;
    auto addLower = [&](const mpq_class& point, bool strict, SatLit reason) {
        if (!lower || point > *lower->point || (point == *lower->point && strict && !lower->strict))
            lower = Endpoint{&point, strict, reason};
    };
    auto addUpper = [&](const mpq_class& point, bool strict, SatLit reason) {
        if (!upper || point < *upper->point || (point == *upper->point && strict && !upper->strict))
            upper = Endpoint{&point, strict, reason};
    };
    for (const auto variable : families_[family].atoms) {
        const auto& atom = atoms_.at(variable);
        const auto position = trail_.find(variable);
        if (!position) continue;
        const auto& entry = trail_[*position];
        if (entry.version != atom.version) continue;
        const auto truth = value(variable, assignment);
        if (!truth || *truth != entry.literal.sign) continue;
        const auto relation = *truth ? atom.relation : negateRelation(atom.relation);
        switch (relation) {
            case Relation::Gt: addLower(atom.endpoint, true, entry.literal); break;
            case Relation::Geq: addLower(atom.endpoint, false, entry.literal); break;
            case Relation::Lt: addUpper(atom.endpoint, true, entry.literal); break;
            case Relation::Leq: addUpper(atom.endpoint, false, entry.literal); break;
            case Relation::Eq:
                addLower(atom.endpoint, false, entry.literal);
                addUpper(atom.endpoint, false, entry.literal);
                break;
            case Relation::Neq: excluded.push_back({&atom.endpoint, entry.literal}); break;
        }
    }
    if (lower && upper && (*lower->point > *upper->point ||
        (*lower->point == *upper->point && (lower->strict || upper->strict)))) {
        pending_.push_back({{lower->reason, upper->reason}, std::nullopt});
        return;
    }
    const bool fixed = lower && upper && *lower->point == *upper->point;
    if (fixed) for (const auto& hole : excluded) if (*hole.point == *lower->point) {
        pending_.push_back({{lower->reason, upper->reason, hole.reason}, std::nullopt});
        return;
    }
    struct Proof { bool truth; std::vector<SatLit> reasons; };
    auto proveUpper = [&](const mpq_class& endpoint, bool strict) -> std::optional<Proof> {
        if (upper && (*upper->point < endpoint ||
            (*upper->point == endpoint && (!strict || upper->strict))))
            return Proof{true, {upper->reason}};
        if (lower && (*lower->point > endpoint ||
            (*lower->point == endpoint && (strict || lower->strict))))
            return Proof{false, {lower->reason}};
        return std::nullopt;
    };
    auto proveEquality = [&](const mpq_class& endpoint) -> std::optional<Proof> {
        if (fixed && *lower->point == endpoint)
            return Proof{true, {lower->reason, upper->reason}};
        if (lower && (*lower->point > endpoint || (*lower->point == endpoint && lower->strict)))
            return Proof{false, {lower->reason}};
        if (upper && (*upper->point < endpoint || (*upper->point == endpoint && upper->strict)))
            return Proof{false, {upper->reason}};
        for (const auto& hole : excluded) if (*hole.point == endpoint)
            return Proof{false, {hole.reason}};
        return std::nullopt;
    };
    for (const auto variable : families_[family].atoms) {
        const auto& atom = atoms_.at(variable);
        std::optional<Proof> proof;
        switch (atom.relation) {
            case Relation::Lt: proof = proveUpper(atom.endpoint, true); break;
            case Relation::Leq: proof = proveUpper(atom.endpoint, false); break;
            case Relation::Geq:
            case Relation::Gt:
                proof = proveUpper(atom.endpoint, atom.relation == Relation::Geq);
                if (proof) proof->truth = !proof->truth;
                break;
            case Relation::Eq: proof = proveEquality(atom.endpoint); break;
            case Relation::Neq:
                proof = proveEquality(atom.endpoint);
                if (proof) proof->truth = !proof->truth;
                break;
        }
        if (!proof) continue;
        const auto current = value(variable, assignment);
        if (current && *current == proof->truth) continue;
        pending_.push_back({std::move(proof->reasons), SatLit{variable, proof->truth}});
    }
}

std::optional<TheoryCheckResult> LinearPredicatePropagation::takePending(
    const TheoryAssignmentView* assignment, TheoryLemmaStorage& lemmas) {
    while (!pending_.empty()) {
        auto inference = std::move(pending_.front());
        pending_.pop_front();
        const bool active = std::all_of(inference.reasons.begin(), inference.reasons.end(),
            [&](SatLit reason) { const auto truth = value(reason.var, assignment);
                return truth && *truth == reason.sign; });
        if (!active) continue;
        const auto conclusionValue = inference.conclusion
            ? value(inference.conclusion->var, assignment) : std::nullopt;
        if (inference.conclusion && conclusionValue && *conclusionValue == inference.conclusion->sign) continue;
        TheoryLemma lemma;
        lemma.kind = LemmaKind::Entailment;
        for (const auto reason : inference.reasons) lemma.lits.push_back(reason.negated());
        if (inference.conclusion) lemma.lits.push_back(*inference.conclusion);
        if (!normalizeTheoryClause(lemma.lits) || lemmas.contains(lemma)) continue;
        if (!inference.conclusion || conclusionValue)
            return TheoryCheckResult::mkConflict(TheoryConflict{std::move(lemma.lits)});
        const auto conclusion = std::find(lemma.lits.begin(), lemma.lits.end(), *inference.conclusion);
        lemma.lits.erase(conclusion);
        lemma.lits.push_back(*inference.conclusion);
        return TheoryCheckResult::mkLemma(std::move(lemma));
    }
    return std::nullopt;
}

std::optional<TheoryCheckResult> LinearPredicatePropagation::check(
    const TheoryAtomRegistry& registry, const TheoryAssignmentView* assignment,
    TheoryLemmaStorage& lemmas) {
    synchronize(registry);
    if (auto result = takePending(assignment, lemmas)) return result;
    while (!dirty_.empty()) {
        const auto family = dirty_.front();
        dirty_.pop_front();
        families_[family].dirty = false;
        derive(family, assignment);
        if (auto result = takePending(assignment, lemmas)) return result;
    }
    return std::nullopt;
}

} // namespace xolver
