#include "theory/arith/idl/IdlSolver.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryLemmaDatabase.h"
#include "theory/arith/dl/DlExplanation.h"
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

static mpz_class mpz_floor(const mpq_class& q) {
    mpz_class result;
    mpz_fdiv_q(result.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
    return result;
}

static mpz_class mpz_ceil(const mpq_class& q) {
    mpz_class result;
    mpz_cdiv_q(result.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
    return result;
}

static bool isInteger(const mpq_class& q) {
    return q.get_den() == 1;
}

// ============================================================================
// IdlSolver
// ============================================================================

IdlSolver::IdlSolver() = default;

void IdlSolver::push() {}

void IdlSolver::pop(uint32_t n) { (void)n; }

void IdlSolver::reset() {
    activeAssignments_.clear();
    disequalities_.clear();
    graph_.clear();
    pendingConflict_.reset();
    pendingLemma_.reset();
}

void IdlSolver::assertLit(const TheoryAtomRecord& atom, bool value, int level, SatLit assertedLit) {
    for (auto& a : activeAssignments_) {
        if (a.atom.satVar == atom.satVar) {
            a = {level, assertedLit, atom, value};
            return;
        }
    }
    activeAssignments_.push_back({level, assertedLit, atom, value});
}

void IdlSolver::backtrackToLevel(int level) {
    auto it = std::remove_if(activeAssignments_.begin(), activeAssignments_.end(),
        [level](const auto& a) { return a.level > level; });
    activeAssignments_.erase(it, activeAssignments_.end());
}

IdlSolver::NormalizeResult IdlSolver::normalizeAndAdd(const ActiveAssignment& a) {
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
            // plus - minus <= rhs  =>  edge minus -> plus weight floor(rhs)
            graph_.addEdge(minusNode, plusNode, mpz_floor(rhs), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Lt: {
            // plus - minus < rhs  =>  plus - minus <= ceil(rhs) - 1
            graph_.addEdge(minusNode, plusNode, mpz_ceil(rhs) - 1, a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Geq: {
            // plus - minus >= rhs  =>  minus - plus <= -ceil(rhs)
            graph_.addEdge(plusNode, minusNode, -mpz_ceil(rhs), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Gt: {
            // plus - minus > rhs  =>  minus - plus <= -(floor(rhs) + 1)
            graph_.addEdge(plusNode, minusNode, -(mpz_floor(rhs) + 1), a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Eq: {
            if (!isInteger(rhs)) {
                return NormalizeResult::ImmediateConflict;
            }
            mpz_class c = rhs.get_num();
            graph_.addEdge(minusNode, plusNode, c, a.lit);
            graph_.addEdge(plusNode, minusNode, -c, a.lit);
            return NormalizeResult::Edges;
        }
        case Relation::Neq: {
            if (!isInteger(rhs)) {
                return NormalizeResult::Tautology;
            }
            disequalities_.push_back({plusVar, minusVar, mpz_class(rhs.get_num()), a.lit});
            return NormalizeResult::Disequality;
        }
    }

    return NormalizeResult::Unsupported;
}

bool IdlSolver::validateModel(const std::vector<mpz_class>& dist) {
    for (const auto& e : graph_.edges()) {
        if (dist[e.to] > dist[e.from] + e.weight) {
            return false;
        }
    }
    for (const auto& d : disequalities_) {
        int plusNode = graph_.nodeByName(d.x);
        int minusNode = graph_.nodeByName(d.y);
        if (plusNode < 0 || minusNode < 0) continue;
        mpz_class diff = dist[plusNode] - dist[minusNode];
        if (diff == d.rhs) return false;
    }
    return true;
}

TheoryLemma IdlSolver::buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaDatabase& lemmaDb) {
    auto lemma = buildDiffLogicDiseqSplitLemma(
        d.x, d.y, d.lit,
        Relation::Leq, Relation::Leq,
        mpq_class(d.rhs - 1), mpq_class(-(d.rhs + 1)),
        TheoryId::IDL, registry_);

    if (lemmaDb.contains(lemma)) return TheoryLemma{};
    lemmaDb.insertIfNew(lemma);
    return lemma;
}

TheoryCheckResult IdlSolver::check(TheoryLemmaDatabase& lemmaDb, TheoryEffort) {
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

    // V1: full rebuild of graph and disequalities from active assignments.
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

    // Run Bellman-Ford
    auto bfResult = bf_.runFull(graph_);
    if (bfResult.negativeCycle) {
        return TheoryCheckResult::mkConflict(
            buildConflict(bfResult.cycle, graph_));
    }

    // Disequality split
    for (const auto& d : disequalities_) {
        int plusNode = graph_.nodeByName(d.x);
        int minusNode = graph_.nodeByName(d.y);
        if (plusNode < 0 || minusNode < 0) continue;
        mpz_class diff = bfResult.dist[plusNode] - bfResult.dist[minusNode];
        if (diff == d.rhs) {
            auto lemma = buildDiseqSplitLemma(d, lemmaDb);
            if (!lemma.lits.empty()) {
                return TheoryCheckResult::mkLemma(lemma);
            }
        }
    }

    // Validate model
    if (!validateModel(bfResult.dist)) {
        return TheoryCheckResult::unknown();
    }

    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
