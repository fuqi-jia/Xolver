#pragma once

#include "expr/ir.h"
#include <gmpxx.h>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

/**
 * ReadOnlyArrayElim — targeted Ackermannization of read-only array reads.
 *
 * TARGETED preprocessing rule (gated XOLVER_TARGETED_PP), aimed at the SV-COMP
 * memory-model family that dominates the failing QF_ANIA / QF_AUFNIA corpus
 * (UltimateAutomizer `#memory_int : (Array Int (Array Int Int))`). In those
 * benchmarks the memory array is **never stored to** on the path that reaches
 * the verification condition — every occurrence is a `(select (select M b) i)`
 * read. The array theory + Nelson-Oppen(array,NIA) combination is engaged for
 * nothing, and the model-based array arrangement search is what times out.
 *
 * Soundness (equisatisfiable, both directions):
 *   With NO `store` / `const-array` and NO array equality anywhere, an array
 *   symbol is an unconstrained (free) function and `select` is an uninterpreted
 *   function. The standard Ackermann reduction then applies: replace each
 *   distinct scalar read by a fresh scalar variable, and add the functional
 *   congruence axiom for each pair of reads on the SAME base array variable
 *   (equal index path ⇒ equal value). Reads on DIFFERENT base array variables
 *   are independent — the arrays are free, so any model of the relaxation
 *   extends to a model of the original by realising the base arrays as distinct
 *   functions; and dropping a never-forced congruence only enlarges the model
 *   set, so UNSAT is preserved too. The result has no array operations, so the
 *   problem drops from QF_ANIA/QF_AUFNIA to QF_(N)IA / QF_UF(N)IA and the strong
 *   pure-arith path solves it.
 *
 * Self-guarding: run() is a no-op (returns false, leaves the IR untouched) the
 * moment it sees a store, a const-array, an array equality, or any array-sorted
 * term in a position other than the array operand of a select. Conservative by
 * construction — when in doubt it does nothing, so it can never change a verdict
 * unsoundly. Only fires on the genuinely read-only fragment.
 *
 * Bottom-up memoized DAG walk; fresh vars via the IR's own hash-cons; never
 * mutates existing nodes. O(#select-pairs-per-base) congruence axioms, with
 * provably-distinct (constant-index) pairs skipped.
 */
class ReadOnlyArrayElim {
public:
    explicit ReadOnlyArrayElim(CoreIr& ir);

    bool run();                 // returns didRewrite()
    void commit();
    bool didRewrite() const { return didRewrite_; }
    // Diagnostics.
    size_t readsEliminated() const { return readVar_.size(); }
    size_t congruencesEmitted() const { return extra_.size(); }

    // Model-reconstruction record for the validator. Each eliminated scalar read
    // `(select arrOperand idxExpr)` was replaced by fresh variable `freshVar`
    // (named `freshName`). Post-solve, the validator re-keys this as a select
    // override (arrOperand-ExprId, value-of-idxExpr) -> value-of-freshVar so the
    // ORIGINAL array-bearing assertions still evaluate concretely. arrOperand /
    // idxExpr are hash-cons-stable inner nodes, identical in the original
    // (pre-const-prop) assertion snapshot the validator walks.
    struct ReadRec {
        ExprId arrOperand;       // the select's array operand (child 0)
        ExprId idxExpr;          // the select's index operand (child 1)
        ExprId freshVar;
        std::string freshName;
    };
    const std::vector<ReadRec>& reads() const { return reads_; }

private:
    CoreIr& ir_;
    bool didRewrite_ = false;
    bool bailed_ = false;

    std::unordered_map<ExprId, ExprId> memo_;
    std::unordered_set<ExprId> inProgress_;
    std::vector<std::pair<int, ExprId>> rewritten_;
    std::vector<ExprId> extra_;                      // Ackermann congruences

    // Key for a scalar read: (baseArrayVar, indexPath outer..inner).
    struct ReadKey {
        ExprId base;
        std::vector<ExprId> path;
        bool operator==(const ReadKey& o) const {
            return base == o.base && path == o.path;
        }
    };
    struct ReadKeyHash {
        std::size_t operator()(const ReadKey& k) const {
            std::size_t h = std::hash<uint32_t>{}(k.base);
            for (ExprId e : k.path)
                h ^= std::hash<uint32_t>{}(e) + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<ReadKey, ExprId, ReadKeyHash> readVar_;   // key -> fresh var
    std::vector<std::pair<ReadKey, ExprId>> readList_;            // for pairwise congruence
    std::vector<ReadRec> reads_;                                  // for model reconstruction

    bool isArraySort(SortId s) const;
    bool intConstVal(ExprId e, mpz_class& out) const;
    // Pre-scan: returns false (and sets bailed_) if anything outside the
    // read-only fragment is present.
    bool safeToEliminate();
    void scanNode(ExprId e, std::unordered_set<ExprId>& seen);
    ExprId rewriteRec(ExprId e);
    // Analyze a scalar select whose children are already rewritten. Returns true
    // and fills `key` when the array operand bottoms out at a base array var via
    // selects only.
    bool analyzeRead(ExprId arr, ExprId idx, ReadKey& key);
    void buildCongruences();
};

} // namespace xolver
