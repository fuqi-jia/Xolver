#include "base/RuntimeConfig.h"
#include "search/linear/BoundAxiomGenerator.h"
#include "base/EnvParam.h"
#include "search/coordination/TheoryAtomRegistry.h"
#include "contracts/LinearFormKey.h"
#include <algorithm>
#include <array>
#include <iterator>
#include <cstdio>
#include <map>
#include <unordered_map>

namespace xolver {
namespace {

Relation flipRelation(Relation relation) {
    switch (relation) {
        case Relation::Leq: return Relation::Geq;
        case Relation::Geq: return Relation::Leq;
        case Relation::Lt: return Relation::Gt;
        case Relation::Gt: return Relation::Lt;
        default: return relation;
    }
}

struct Predicate {
    Relation relation;
    mpq_class endpoint;
    SatLit literal;
};

struct Family {
    TheoryId theory;
    LinearFormKey form;
    std::vector<Predicate> predicates;
};

// At a shared endpoint, the open half-line precedes the closed half-line:
// (L < c) implies (L <= c). Between endpoints, the rational order is exact.
struct Cut {
    mpq_class endpoint;
    bool closed;
    bool operator<(const Cut& other) const {
        if (endpoint != other.endpoint) return endpoint < other.endpoint;
        return closed < other.closed;
    }
};

} // namespace

std::size_t BoundAxiomGenerator::generate(TheoryAtomRegistry& registry, SatSolver& sat) {
    std::array<std::unordered_map<LinearFormKey, std::size_t, LinearFormKeyHash>, 2> indices;
    std::vector<Family> families;
    // Snapshot before registering missing endpoints; registration can reallocate
    // registry.records(). Keep domain ownership for each synthesized predicate.
    for (const auto& record : registry.records()) {
        if ((record.theory != TheoryId::LIA && record.theory != TheoryId::LRA) ||
            !std::holds_alternative<LinearAtomPayload>(record.payload)) continue;
        const auto& payload = std::get<LinearAtomPayload>(record.payload);
        if (!payload.rhs.isRational() || payload.lhs.terms.empty()) continue;
        auto form = payload.lhs;
        auto relation = payload.rel;
        mpq_class endpoint = payload.rhs.asRational();
        if (form.terms.front().second < 0) {
            for (auto& term : form.terms) term.second = -term.second;
            endpoint = -endpoint;
            relation = flipRelation(relation);
        }
        auto& index = indices[record.theory == TheoryId::LIA ? 0 : 1];
        const auto [position, inserted] = index.try_emplace(form, families.size());
        if (inserted) families.push_back({record.theory, std::move(form), {}});
        families[position->second].predicates.push_back({relation, std::move(endpoint),
                                                        SatLit::positive(record.satVar)});
    }

    std::size_t emitted = 0, compiled = 0, totalAtoms = 0, maximum = 0;
    auto imply = [&](SatLit premise, SatLit conclusion) {
        if (premise == conclusion) return;
        sat.addTheoryClause({premise.negated(), conclusion});
        ++emitted;
    };
    for (const auto& family : families) {
        const auto size = family.predicates.size();
        totalAtoms += size;
        maximum = std::max(maximum, size);
        // One predicate has no relationship to another registered literal.
        if (size < 2) continue;
        ++compiled;
        std::map<Cut, SatLit> cuts;
        auto addCut = [&](const mpq_class& endpoint, bool closed, SatLit literal) {
            const auto [position, inserted] = cuts.try_emplace(Cut{endpoint, closed}, literal);
            if (!inserted) {
                imply(literal, position->second);
                imply(position->second, literal);
            }
        };
        for (const auto& predicate : family.predicates) {
            switch (predicate.relation) {
                case Relation::Lt: addCut(predicate.endpoint, false, predicate.literal); break;
                case Relation::Leq: addCut(predicate.endpoint, true, predicate.literal); break;
                case Relation::Geq: addCut(predicate.endpoint, false, predicate.literal.negated()); break;
                case Relation::Gt: addCut(predicate.endpoint, true, predicate.literal.negated()); break;
                default: break;
            }
        }
        auto endpointLiteral = [&](const mpq_class& endpoint, bool closed) {
            const auto found = cuts.find(Cut{endpoint, closed});
            if (found != cuts.end()) return found->second;
            const auto literal = registry.getOrCreateLinearBoundAtom(family.form,
                closed ? Relation::Leq : Relation::Lt, endpoint, family.theory);
            cuts.emplace(Cut{endpoint, closed}, literal);
            return literal;
        };
        for (const auto& predicate : family.predicates) {
            if (predicate.relation != Relation::Eq && predicate.relation != Relation::Neq) continue;
            const auto equality = predicate.relation == Relation::Eq
                ? predicate.literal : predicate.literal.negated();
            const auto open = endpointLiteral(predicate.endpoint, false);
            const auto closed = endpointLiteral(predicate.endpoint, true);
            // (L = c) iff !(L < c) and (L <= c). These are arithmetic
            // tautologies over registered atoms, including both polarities.
            imply(equality, open.negated());
            imply(equality, closed);
            sat.addTheoryClause({equality, open, closed.negated()});
            ++emitted;
        }
        if (!cuts.empty()) {
            auto previous = cuts.begin();
            for (auto current = std::next(previous); current != cuts.end(); ++current) {
                imply(previous->second, current->second);
                previous = current;
            }
        }
    }
    if (config::read<config::ReadKind::Boolean>("XOLVER_LRA_BOUND_AXIOMS_DIAG")) {
        std::fprintf(stderr,
            "[BOUND-AX] linAtoms=%zu groups=%zu pairedGroups=%zu maxGroup=%zu clauses=%zu\n",
            totalAtoms, families.size(), compiled, maximum, emitted);
    }
    return emitted;
}

} // namespace xolver
