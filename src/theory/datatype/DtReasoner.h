#pragma once

#include "expr/types.h"
#include "theory/euf/EufTypes.h"
#include <vector>
#include <string>
#include <optional>
#include <unordered_set>
#include <unordered_map>
#include <cstdint>

namespace zolver {

class EufTermManager;
class IncrementalEGraph;
class CoreIr;
class TheoryAtomRegistry;

// ---------------------------------------------------------------------------
// DtReasoner — algebraic-datatype axiom reasoning on the shared EUF egraph.
//
// Owned by EufSolver, layered on the SAME IncrementalEGraph (mirrors
// ArrayReasoner). Constructor / selector / tester terms are interned as
// ordinary uninterpreted applications (distinct, name-bearing symbols), so
// congruence + dedup are free. This class adds the free-algebra axioms
// (Reynolds–Blanchette, IJCAI'16) as theory lemmas and egraph-proof conflicts:
//
//   clash         C(a..) = D(b..), C != D            -> CONFLICT
//   acyclicity    x = C(... x ...)  (recursive DT)   -> CONFLICT
//   injectivity   C(a..) = C(b..)   =>  a_i = b_i     -> lemma (full effort)
//   projection    is/known C: sel_i^C(C(a..)) = a_i  -> lemma (full effort)
//
// SOUNDNESS:
//  * Conflicts use egraph explainEquality reason sets (complete explanations).
//  * Selectors are GUARDED: projection fires only when the operand's class
//    holds a constructor term of the selector's OWN constructor; a selector on
//    the wrong/unknown constructor (head(nil)) is underspecified, never a
//    conflict.
//  * This procedure detects UNSAT soundly but is NOT a complete SAT decision
//    procedure here (no exhaustiveness split / model construction). DT-logic
//    SAT verdicts are floored to unknown by the Solver unless DT-validated.
//
// All term-keyed state is monotonic (EUF term ids are never reused), so it does
// not need rollback; conflicts/lemmas are recomputed each check() against the
// live (rolled-back) egraph.
// ---------------------------------------------------------------------------
class DtReasoner {
public:
    DtReasoner() = default;

    void setContext(EufTermManager* tm, IncrementalEGraph* egraph,
                    const CoreIr* ir, TheoryAtomRegistry* registry) {
        tm_ = tm;
        egraph_ = egraph;
        ir_ = ir;
        registry_ = registry;
    }

    // The egraph's Bool true/false constant terms, needed for tester evaluation.
    void setBoolConstants(EufTermId trueTerm, EufTermId falseTerm) {
        trueTerm_ = trueTerm;
        falseTerm_ = falseTerm;
    }

    // In Nelson-Oppen combination (QF_UFDTNIA/QF_UFDTLIA) a FINITE datatype
    // (enum / all-finite-field, non-recursive) is not stably infinite, so plain
    // N-O is incomplete (polite combination is required — plan §3). When set,
    // modelFullyDetermined() refuses to certify a model that involves a finite
    // datatype, flooring such combination cases to unknown (sound). Pure QF_UFDT
    // (no combination) is decidable on its own and is never floored.
    void setCombinationMode(bool b) { combinationMode_ = b; }

    bool active() const { return tm_ != nullptr && egraph_ != nullptr && ir_ != nullptr; }

    // Completeness certificate (const): every interned datatype-sorted term's
    // e-class contains a constructor term. When this holds AND the last check()
    // was Consistent (no clash/injectivity/projection/tester/acyclicity
    // conflict), the DT structure is a concrete ground-term model, so a `sat`
    // verdict is SOUND (no exhaustiveness split or model validation needed). If
    // some datatype class has no determined constructor, the procedure is
    // incomplete here -> the caller floors to unknown.
    bool modelFullyDetermined() const;

    void reset();

    // Scan newly interned terms for DT operators. Idempotent, monotonic.
    bool discoverDtTerms();

    // Sound UNSAT detection against the current (congruence-closed) egraph:
    // constructor clash and, for recursive datatypes, acyclicity. Returns the
    // conflict clause literals (each currently TRUE in the SAT assignment) or
    // nullopt. Safe at any effort.
    std::optional<std::vector<SatLit>> checkConflict();

    // Produce one injectivity or guarded-projection lemma if a fresh instance
    // exists (full effort). Returns lemma literals (SAT polarity) or nullopt.
    std::optional<std::vector<SatLit>> instantiateLemma();

private:
    EufTermManager* tm_ = nullptr;
    IncrementalEGraph* egraph_ = nullptr;
    const CoreIr* ir_ = nullptr;
    TheoryAtomRegistry* registry_ = nullptr;

    // Discovered DT terms (monotonic, never rolled back).
    std::vector<EufTermId> ctorTerms_;
    std::vector<EufTermId> selectorTerms_;
    std::vector<EufTermId> testerTerms_;
    std::unordered_set<EufTermId> ctorSet_;
    std::unordered_set<EufTermId> selectorSet_;
    std::unordered_set<EufTermId> testerSet_;
    EufTermId nextTermToScan_ = 0;

    EufTermId trueTerm_ = NullEufTerm;
    EufTermId falseTerm_ = NullEufTerm;
    bool combinationMode_ = false;

    // Lemma dedup keyed by stable term ids.
    std::unordered_set<uint64_t> injectivityDone_;   // (ctorTerm1, ctorTerm2) << argIndex folded in
    std::unordered_set<uint64_t> projectionDone_;     // (selectorTerm, ctorTerm)

    bool symIsConstructor(EufTermId t) const;
    bool symIsSelector(EufTermId t) const;
    bool symIsTester(EufTermId t) const;

    // A sort is finite iff: Bool, or a non-recursive datatype all of whose
    // field sorts are finite. Int/Real/Array/uninterpreted are treated as
    // infinite (stably infinite for N-O). Used for the finite-DT combination
    // floor. `visiting` guards mutual recursion.
    bool isFiniteSort(SortId s, std::unordered_set<SortId>& visiting) const;

    // The CoreExpr origin of a term (or NullExpr).
    ExprId originExpr(EufTermId t) const;
    // Operator name carried by a DT term's origin payload ("" if none).
    std::string opName(EufTermId t) const;
    // Datatype sort of a constructor term (its origin sort).
    SortId ctorSort(EufTermId t) const;

    // Acyclicity: DFS over constructor edges (class -> class of each
    // datatype-sorted constructor argument) looking for a cycle. On a cycle,
    // fills `reasons` with the explainEquality literals linking the chain.
    std::optional<std::vector<SatLit>> checkAcyclicity();

    static uint64_t pairKey(uint32_t a, uint32_t b) {
        return (static_cast<uint64_t>(a) << 32) | static_cast<uint64_t>(b);
    }
};

} // namespace zolver
