#include "theory/arith/idl/IdlSolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/arith/dl/DlExplanation.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/arith/linear/DiffLogicDiseqSplitter.h"
#include <algorithm>
#include <cassert>
#include <iostream>

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

void IdlSolver::onReset() {
    // Base clears the trail; clear IDL-specific graph state here.
    disequalities_.clear();
    graph_.clear();
}

IdlSolver::NormalizeResult IdlSolver::normalizeAndAdd(const ActiveAssignment& a) {
    const auto* payload = std::get_if<LinearAtomPayload>(&a.atom.payload);
    if (!payload) return NormalizeResult::Unsupported;

    Relation rel = a.value ? payload->rel : negateRel(payload->rel);
    mpq_class rhs = payload->rhs;
    const auto& terms = payload->lhs.terms;

    std::cerr << "[IDL-ASSERT-LIT] sat_var=" << a.atom.satVar
              << " sat_lit=" << (a.lit.sign ? "" : "-") << a.lit.var
              << " polarity=" << (a.value ? "POS" : "NEG")
              << " stored_rel=" << (int)payload->rel
              << " effective_rel=" << (int)rel
              << " rhs=" << rhs.get_str()
              << " terms=";
    for (const auto& [name, coeff] : terms) {
        std::cerr << name << ":" << coeff.get_str() << " ";
    }
    std::cerr << "\n";

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

TheoryLemma IdlSolver::buildDiseqSplitLemma(const DiseqInfo& d, TheoryLemmaStorage& lemmaDb) {
    auto lemma = buildDiffLogicDiseqSplitLemma(
        d.x, d.y, d.lit,
        Relation::Leq, Relation::Leq,
        mpq_class(d.rhs - 1), mpq_class(-(d.rhs + 1)),
        TheoryId::IDL, registry_);

    // Only suppress if the lemma has been successfully installed into SAT.
    // A lemma that was generated but never flushed must be returned again.
    if (lemmaDb.isInstalled(lemma)) return TheoryLemma{};
    lemmaDb.insertIfNew(lemma);
    return lemma;
}

TheoryCheckResult IdlSolver::check(TheoryLemmaStorage& lemmaDb, TheoryEffort) {
    if (hasPending()) return drainPending();

    // V1: full rebuild of graph and disequalities from active assignments.
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
        // Disequality violated: try to return a repair lemma before giving up.
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
        return TheoryCheckResult::unknown();
    }

    return TheoryCheckResult::consistent();
}

} // namespace nlcolver
