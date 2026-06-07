#pragma once

#include "expr/ir.h"
#include "theory/core/TheorySolver.h"
#include <gmpxx.h>
#include <chrono>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * CandidateModelSearch (Capability 10 of the close-all-known-fails plan).
 *
 * SAT-only validated witness search. Last resort after every legacy
 * complete engine returns Unknown.
 *
 * **Soundness contract**: this class never produces UNSAT, Conflict, or
 * Lemma. It generates candidate assignments using a small set of
 * deterministic strategies, then accepts a candidate only if a complete
 * arithmetic evaluator over the original assertions reports that every
 * assertion holds.
 *
 * Strategies (executed in this order):
 *
 *   10a. Low-height rational enumeration over a per-variable priority
 *        list (0, 1, -1, 1/2, -1/2, 2, -2, ...). The Cartesian product
 *        is explored in increasing total-height order so simple
 *        witnesses (e.g. (1, 0, 0)) appear within the per-strategy
 *        budget.
 *
 *   10d. Symmetric diagonal: detect syntactic permutation symmetry over
 *        the variables and try x = y = ... = c for c in
 *        {-2, -1, 0, 1, 2}.
 *
 *   10c. Boundary points: for each integer variable with an active
 *        interval [L, U] (detected by a lightweight syntactic scan
 *        of the assertions), try L, L+1, U, U-1.
 *
 *   10b. Linear-skeleton feasibility witness (delegated to
 *        GeneralSimplex if available; otherwise the strategy yields
 *        no candidate).
 *
 * Budgets:
 *   - candidates per strategy:        200
 *   - rational denominator bound:     12
 *   - absolute numerator bound:       10
 *   - wall-clock per invocation:      50 ms
 *
 * Validation:
 *   - Construct a complete assignment over every free numeric variable
 *     (defaulting unconstrained variables to 0 or the midpoint of an
 *     active bound).
 *   - Recursively evaluate every original assertion under the
 *     assignment. Each atom must evaluate to a definite boolean; any
 *     unresolvable construct (UF outside whitelist, division by an
 *     unpinned divisor) discards the candidate.
 *   - Returns the complete assignment for the first candidate that
 *     evaluates every assertion to `true`.
 *
 * Pure arithmetic logics are enabled by default. UF-bearing logics
 * (QF_UFNIA / QF_UFNRA / etc.) are disabled until the arithmetic
 * evaluator's UF interpretation is extended; this guards against
 * unsoundness from inconsistent UF interpretations in a candidate
 * extension.
 */
class CandidateModelSearch {
public:
    struct Result {
        bool found = false;
        TheorySolver::TheoryModel model;
        std::string strategy;
    };

    struct Config {
        // Per-strategy candidate budget. The wall-clock budget is the
        // hard real-time limit; the candidate budget is a soft cap to
        // protect against pathological symmetric assertions where every
        // height is reachable from the same triple. 5000 lets the Int
        // enumeration reach total height 6 (cumulative ~370 triples),
        // which covers nia_048's (3, 2, 1) witness.
        size_t maxCandidatesPerStrategy = 5000;
        int64_t denominatorBound = 12;
        int64_t numeratorBound = 10;
        std::chrono::milliseconds wallClockBudget{200};
        // When non-empty, the search collects variables, bounds, and
        // validates against THESE assertion roots instead of ir.assertions().
        // Used by the Solver's validated model-repair to search over the
        // ORIGINAL (pre-lowering) assertions — the lowered form introduces
        // __nlc_ auxiliaries (to_int floor vars, etc.) that the search skips
        // but the lowered assertions still reference, leaving every candidate
        // indeterminate.
        std::vector<ExprId> assertionRootsOverride;
        // When true, the search also models uninterpreted functions: each
        // numeric-sorted application f(args) becomes a value slot, functional
        // consistency (equal arg tuples -> equal value) is enforced during
        // validation, and a function table is emitted in the model. Enables
        // QF_UF* logics. Off by default so the verdict-path invocation (Cap.
        // 10 last resort) keeps its conservative UF-free behavior; only the
        // Solver's sat-model repair turns it on.
        bool allowUF = false;
        Config() = default;
    };

    CandidateModelSearch(const CoreIr& ir, std::string_view logic);
    CandidateModelSearch(const CoreIr& ir, std::string_view logic,
                         const Config& cfg);

    // Returns a validated SAT witness or `Result{found=false}`.
    Result run();

private:
    struct VarRecord {
        ExprId exprId;
        std::string name;
        SortId sort;
        // Set for a synthetic value slot standing in for a UF application
        // f(args). exprId is the application node; funcName is f. The slot is
        // enumerated like a variable but written to the function table, not
        // the variable assignment, on accept.
        bool isApp = false;
        std::string funcName;
        // Value forced by a top-level equality (= f(consts) c) — the base-case
        // axioms (pow2(0)=1 ...). Pinned slots seed the DERIVATION of symbolic
        // apps (pow2(k) with k=1 matches pow2(1) by functional consistency).
        // This is the cvc5/z3 model-construction idea (assignFunctionDefault /
        // func_interp): a UF app whose evaluated args match a known app takes
        // that value; otherwise it keeps a default. See deriveAppValues.
        std::optional<mpq_class> pinnedValue;
    };

    void collectFreeVariables();
    // Pin UF-app slots whose value a top-level equality forces to a constant.
    void pinForcedAppSlots();
    // cvc5/z3-style model construction: DERIVE each UF-app slot's value from the
    // arith assignment (pinned base cases + functional consistency) instead of
    // ENUMERATING it. Mutates `full`. Sound: re-validated by evaluateAssertions.
    void deriveAppValues(std::unordered_map<std::string, mpq_class>& full) const;
    // Diagnostic rejection breakdown (XOLVER_DIAG_CMS): how candidates were
    // disposed of, to tell "never generated" from "generated and rejected".
    mutable size_t diagTried_ = 0, diagFcReject_ = 0, diagEvalFalse_ = 0,
                   diagEvalIndet_ = 0, diagAccept_ = 0;
    void buildPriorityList();
    void detectActiveBounds();
    bool isLogicEnabled() const;

    // The assertion roots to search over: cfg_.assertionRootsOverride when
    // set, otherwise ir_.assertions().
    std::vector<ExprId> assertionRoots() const;

    // Strategies. Each appends candidate assignments to candidates_ until
    // the per-strategy budget is exhausted or the wall-clock deadline is
    // reached. Validation happens after each candidate is generated, and
    // the first valid candidate short-circuits the whole search.
    bool runStrategy10a();
    bool runStrategy10c();
    bool runStrategy10d();

    // Evaluate the assertion list against `assignment`. Returns Yes/No/
    // Indeterminate.
    enum class EvalVerdict { True, False, Indeterminate };
    EvalVerdict evaluateAssertions(
        const std::unordered_map<std::string, mpq_class>& assignment) const;

    enum class TermVerdict { Bool, Number, Indeterminate };
    struct TermResult {
        TermVerdict kind = TermVerdict::Indeterminate;
        bool boolValue = false;
        mpq_class numValue = 0;
    };
    TermResult evalTerm(
        ExprId eid,
        const std::unordered_map<std::string, mpq_class>& assignment) const;
    // Top-level entry: pre-warms evalMemo_ bottom-up (iterative) so the recursive
    // evalTerm resolves every subterm from the memo and never recurses deeply
    // (deep-term stack-overflow guard). All external callers use this.
    TermResult evalTermTop(
        ExprId eid,
        const std::unordered_map<std::string, mpq_class>& assignment) const;
    // Memo populated by evalTermTop's pre-pass; consulted at evalTerm's entry.
    // Keyed by ExprId, valid only within one assignment (cleared per top call).
    mutable std::unordered_map<ExprId, TermResult> evalMemo_;

    bool detectSymmetry() const;
    static int64_t heightOf(const mpq_class& q);

    // UF support (only active when cfg_.allowUF). Collect numeric-sorted
    // application nodes as value slots, reject candidates that break
    // functional consistency, and emit a function table for an accepted one.
    void collectApplicationSlots();
    bool functionallyConsistent(
        const std::unordered_map<std::string, mpq_class>& full) const;
    void buildFunctionInterps(
        const std::unordered_map<std::string, mpq_class>& full);

    // Acceptance: validate a candidate (extending unspecified variables
    // to a default value) and, on success, record the model in result_.
    bool tryAcceptCandidate(
        const std::unordered_map<std::string, mpq_class>& partial,
        const std::string& strategyName);

    const CoreIr& ir_;
    std::string logic_;
    Config cfg_;
    std::chrono::steady_clock::time_point deadline_;

    std::vector<VarRecord> vars_;
    std::unordered_map<std::string, size_t> varIndexByName_;
    std::vector<mpq_class> priority_;            // shared priority list
    std::vector<std::vector<mpq_class>> perVar_; // per-variable values

    struct BoundInfo {
        std::optional<mpq_class> lower;
        std::optional<mpq_class> upper;
        bool lowerStrict = false;
        bool upperStrict = false;
    };
    std::unordered_map<std::string, BoundInfo> activeBounds_;

    Result result_;
    size_t totalCandidatesTried_ = 0;
};

} // namespace xolver
