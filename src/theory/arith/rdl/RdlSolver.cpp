#include "theory/arith/rdl/RdlSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/dl/DlExplanation.h"
#include "theory/arith/dl/DlModel.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/linear/DiffLogicDiseqSplitter.h"
#include <algorithm>
#include <cassert>

namespace zolver {

// ============================================================================
// Helpers
// ============================================================================

static Relation negateRel(Relation r) {
    switch (r) {
        case Relation::Leq: return Relation::Gt;
        case Relation::Lt:  return Relation::Geq;
        case Relation::Geq: return Relation::Lt;
        case Relation::Gt:  return Relation::Leq;
        case Relation::Eq:  return Relation::Neq;
        case Relation::Neq: return Relation::Eq;
    }
    return r;
}

// ============================================================================
// RdlSolver
// ============================================================================

RdlSolver::RdlSolver() = default;

void RdlSolver::onReset() {
    // Base clears the trail; clear RDL-specific graph state here.
    disequalities_.clear();
    graph_.clear();
    haveModel_ = false;
    lastModel_.clear();
}

void RdlSolver::onBacktrack(int targetLevel) {
    (void)targetLevel;
    haveModel_ = false;  // model is valid only for the assignment that built it
}

std::optional<RdlSolver::TheoryModel> RdlSolver::getModel() const {
    if (!haveModel_) return std::nullopt;
    TheoryModel model;
    for (const auto& [name, val] : lastModel_) {
        if (name.empty()) continue;
        if (name.size() >= 2 && name[0] == '_' && name[1] == '_') continue;  // __ZERO__ / internal
        model.assignments[name] = val.get_str();
        model.numericAssignments.insert({name, RealValue::fromMpq(val)});
    }
    if (model.assignments.empty()) return std::nullopt;
    return model;
}

RdlSolver::NormalizeResult RdlSolver::normalizeAndAdd(const ActiveAssignment& a) {
    const auto* payload = std::get_if<LinearAtomPayload>(&a.atom.payload);
    if (!payload) return NormalizeResult::Unsupported;

    Relation rel = a.value ? payload->rel : negateRel(payload->rel);
    auto rhsQ = payload->rhs.tryAsRational();
    if (!rhsQ) return NormalizeResult::Unsupported;  // algebraic RHS: never from inputs
    mpq_class rhs = *rhsQ;
    const auto& terms = payload->lhs.terms;

    // Orient + scale. Accept any difference constraint a*p - a*q (rel) rhs,
    // including non-unit (a != 1) and single-variable scaled forms, by dividing
    // through by the common magnitude. Orienting the positive-coefficient var as
    // plusVar and the negative as minusVar absorbs the sign, so the relation is
    // never flipped. Real domain: exact rational division, no rounding. All
    // arithmetic is exact mpq_class.
    std::string plusVar, minusVar;
    mpq_class plusCoeff(0), minusCoeff(0);
    for (const auto& [name, coeff] : terms) {
        if (coeff == 0) continue;
        if (coeff > 0) {
            if (!plusVar.empty()) return NormalizeResult::Unsupported;  // >1 positive var
            plusVar = name; plusCoeff = coeff;
        } else {
            if (!minusVar.empty()) return NormalizeResult::Unsupported; // >1 negative var
            minusVar = name; minusCoeff = coeff;
        }
    }

    // All-zero / empty: not a difference constraint. Bail explicitly before any
    // node creation so we never build an illegal zero-node edge.
    if (plusVar.empty() && minusVar.empty()) {
        return NormalizeResult::Unsupported;
    }

    mpq_class mag;
    if (!plusVar.empty() && !minusVar.empty()) {
        // Two vars: require the antisymmetric form a*p - a*q (exact comparison).
        if (plusCoeff + minusCoeff != 0) return NormalizeResult::Unsupported;
        mag = plusCoeff;            // > 0
    } else if (!plusVar.empty()) {
        // Single positive var a*p: plus = p, minus = ZERO.
        mag = plusCoeff;            // > 0
        minusVar = "__ZERO__";
    } else {
        // Single negative var -a*q: plus = ZERO, minus = q.
        mag = -minusCoeff;          // > 0
        plusVar = "__ZERO__";
    }

    // Divide through by the positive magnitude; relation stays as-is.
    rhs /= mag;

    int plusNode = graph_.getOrCreateNode(plusVar);
    int minusNode = graph_.getOrCreateNode(minusVar);

    switch (rel) {
        case Relation::Leq: {
            // plus - minus <= rhs  =>  edge minus -> plus weight (rhs, 0)
            graph_.addEdge(minusNode, plusNode, RdlWeight(rhs, 0), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Lt: {
            // plus - minus < rhs  =>  edge minus -> plus weight (rhs, -1)
            graph_.addEdge(minusNode, plusNode, RdlWeight(rhs, -1), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Geq: {
            // plus - minus >= rhs  =>  minus - plus <= -rhs
            graph_.addEdge(plusNode, minusNode, RdlWeight(-rhs, 0), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Gt: {
            // plus - minus > rhs  =>  minus - plus < -rhs
            graph_.addEdge(plusNode, minusNode, RdlWeight(-rhs, -1), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Eq: {
            graph_.addEdge(minusNode, plusNode, RdlWeight(rhs, 0), a.lit);
            graph_.addEdge(plusNode, minusNode, RdlWeight(-rhs, 0), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Neq: {
            disequalities_.push_back({plusVar, minusVar, rhs, a.lit});
            return NormalizeResult::Disequality;
        }
    }

    return NormalizeResult::Unsupported;
}

bool RdlSolver::validateModel(const std::vector<RdlWeight>& dist) {
    for (const auto& e : graph_.edges()) {
        RdlWeight sum = dist[e.from] + e.weight;
        if (sum < dist[e.to]) {
            return false;
        }
    }
    return true;
}

TheoryLemma RdlSolver::buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaStorage& lemmaDb) {
    auto lemma = buildDiffLogicDiseqSplitLemma(
        d.x, d.y, d.lit,
        Relation::Lt, Relation::Lt,
        d.rhs, -d.rhs,
        TheoryId::RDL, registry_);

    if (lemmaDb.isInstalled(lemma)) return TheoryLemma{};
    lemmaDb.insertIfNew(lemma);
    return lemma;
}

TheoryCheckResult RdlSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    haveModel_ = false;
    if (hasPending()) return drainPending();

    graph_.clear();
    disequalities_.clear();

    for (const auto& a : trail()) {
        auto r = normalizeAndAdd(a);
        switch (r) {
            case NormalizeResult::Unsupported:
                return TheoryCheckResult::unknown();
            case NormalizeResult::ImmediateConflict:
                return TheoryCheckResult::mkConflict(
                    TheoryConflict{{a.lit}});
            case NormalizeResult::Tautology:
                continue;
            case NormalizeResult::Edges:
            case NormalizeResult::Disequality:
                break;
        }
    }

    auto bfResult = bf_.runFull(graph_);
    if (bfResult.negativeCycle) {
        return TheoryCheckResult::mkConflict(
            buildConflict(bfResult.cycle, graph_));
    }

    // Validate lexicographic distances (sanity check)
    if (!validateModel(bfResult.dist)) {
        return TheoryCheckResult::unknown();
    }

    // Build concrete rational model
    auto modelOpt = buildRdlModel(bfResult.dist, graph_.zeroNode(), graph_);
    if (!modelOpt) {
        return TheoryCheckResult::unknown();
    }

    // Disequality split
    for (const auto& d : disequalities_) {
        auto itX = modelOpt->find(d.x);
        auto itY = modelOpt->find(d.y);
        if (itX == modelOpt->end() || itY == modelOpt->end()) continue;
        if (itX->second - itY->second == d.rhs) {
            auto lemma = buildDiseqSplitLemma(d, lemmaDb);
            if (!lemma.lits.empty()) {
                return TheoryCheckResult::mkLemma(lemma);
            }
            // Lemma already installed but model still violates disequality.
            // This should not happen if the SAT solver respects the lemma.
            return TheoryCheckResult::unknown();
        }
    }

    // Consistent: keep the concrete rational model for read-off.
    lastModel_ = std::move(*modelOpt);
    haveModel_ = true;
    return TheoryCheckResult::consistent();
}

} // namespace zolver
