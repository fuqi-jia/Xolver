#include "theory/arith/rdl/RdlSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/dl/DlExplanation.h"
#include "theory/arith/dl/DlModel.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/linear/DiffLogicDiseqSplitter.h"
#include <algorithm>
#include <cassert>

namespace nlcolver {

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

void RdlSolver::push() {}

void RdlSolver::pop(uint32_t n) { (void)n; }

void RdlSolver::reset() {
    activeAssignments_.clear();
    disequalities_.clear();
    graph_.clear();
    pendingConflict_.reset();
    pendingLemma_.reset();
}

void RdlSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void RdlSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
}

RdlSolver::NormalizeResult RdlSolver::normalizeAndAdd(const ActiveAssignment& a) {
    const auto* payload = std::get_if<LinearAtomPayload>(&a.atom.payload);
    if (!payload) return NormalizeResult::Unsupported;

    Relation rel = a.value ? payload->rel : negateRel(payload->rel);
    mpq_class rhs = payload->rhs;
    const auto& terms = payload->lhs.terms;

    // Identify +1 and -1 variables.
    std::string plusVar, minusVar;
    for (const auto& [name, coeff] : terms) {
        if (coeff == 1) plusVar = name;
        else if (coeff == -1) minusVar = name;
        else return NormalizeResult::Unsupported;
    }

    // Single-variable forms map ZERO as the other side.
    if (terms.size() == 1) {
        if (!plusVar.empty()) {
            minusVar = "__ZERO__";
        } else {
            plusVar = "__ZERO__";
        }
    }

    if (plusVar.empty() || minusVar.empty()) {
        return NormalizeResult::Unsupported;
    }

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
    if (pendingConflict_) {
        auto c = *pendingConflict_;
        pendingConflict_.reset();
        return TheoryCheckResult::mkConflict(c);
    }
    if (pendingLemma_) {
        auto l = *pendingLemma_;
        pendingLemma_.reset();
        return TheoryCheckResult::mkLemma(l);
    }

    graph_.clear();
    disequalities_.clear();

    for (const auto& a : activeAssignments_) {
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

    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
