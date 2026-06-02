// Farkas-Or Phase 2a: support table + GAC-style backtrack.
//
// This is the prototype CSP layer over (B-domains, choice-domains, CT-
// interval). For each (block_j, branch_k) we precompute a table of all
// B-tuples under which the branch is feasible (via P1's solveBranch),
// together with the resulting λ-ray and CT bounds.
//
// The solver runs a backtrack search:
//   pick the next undecided variable (smallest domain first);
//   for each value w in D(var):
//     tentatively assign var = w;
//     forward-check: for each block, prune branches whose support
//                    becomes empty under the new domains;
//     intersect-check: for each forced-choice block, intersect CT
//                      with the chosen branch's CT bound;
//     if any domain becomes empty: undo and try next w.
//   on full assignment: emit (B, choices, CT-interval). P3 then runs
//   the residual LIA check on the remaining linear constraints;
//   P4 validates the assembled integer model against the original
//   CoreIr formula.
//
// Soundness: this lane returns SAT only (validated by P4 against the
// original formula). It NEVER returns UNSAT — a failed CSP search just
// means no model was constructed; the rest of the NIA pipeline takes
// over.

#pragma once

#include "expr/ir.h"
#include "theory/arith/nia/farkas/FarkasOrBranchSolver.h"
#include "theory/arith/nia/farkas/FarkasOrTypes.h"
#include <gmpxx.h>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace xolver::farkas {

// One row of the support table.
struct SupportRow {
    int blockIdx = -1;
    int branchIdx = -1;
    // Bounded-var values keyed by name (only the bounded vars that
    // ACTUALLY appear in this branch's atoms — not all bounded globals).
    std::map<std::string, mpz_class> bTuple;
    BranchCandidate candidate;
    // For non-empty residValues, the row carries the (B, resid) pair that
    // P1 used to make the branch feasible. The CSP layer treats residuals
    // as branch-local — different rows of the same (block, branch) may
    // have different resid values, and matching against a chosen B-tuple
    // picks the row whose B matches; the row's resid then feeds back to
    // the assembler.
};

struct SupportTable {
    // Canonical order of bounded global vars.
    std::vector<std::string> boundedVarOrder;
    // Per-bounded-var initial domain.
    std::map<std::string, std::vector<mpz_class>> initialBDomain;
    // CT-like vars.
    std::vector<std::string> ctVars;
    // Per (block, branch) → list of feasible support rows.
    std::map<std::pair<int, int>, std::vector<std::size_t>> byBlockBranch;
    // All rows.
    std::vector<SupportRow> rows;
    // Size of the table (#feasible (block, branch, B) triples).
    std::size_t feasibleTotal = 0;
};

// Final assignment produced by solveCsp.
struct FarkasOrAssignment {
    std::map<std::string, mpz_class> B;          // bounded global values
    std::map<int, int> choice;                   // choice per block (block idx → branch idx)
    std::map<int, std::vector<mpz_class>> rayPerBlock;        // (scaleT applied if needed in P3)
    std::map<int, std::vector<std::string>> lambdaNamesPerBlock;
    std::map<std::string, std::pair<mpq_class, mpq_class>> ctInterval;  // per CT var
    std::map<std::string, std::pair<bool, bool>> ctFinite;
    // Per-block residual co-var values committed by the chosen support row.
    // These get merged into the IntegerModel by the assembler. Different
    // blocks may write to overlapping residual var names; we keep the LAST
    // write (assembler merges into a single map).
    std::map<int, std::unordered_map<std::string, mpz_class>> residPerBlock;
};

class FarkasOrSolver {
public:
    explicit FarkasOrSolver(const CoreIr& ir) : ir_(ir), p1_(ir) {}

    // Build support table by precomputing for every (block, branch, B)
    // triple. The B cartesian product must be ≤ maxBProduct or the
    // build returns an empty table (signal: too large for P2a, P2b
    // territory).
    SupportTable buildTable(const FarkasProfile& profile,
                            std::size_t maxBProduct = 5000) const;

    // Run the GAC-style backtrack search. Returns the first satisfying
    // assignment if one exists, std::nullopt otherwise.
    std::optional<FarkasOrAssignment>
    solveCsp(const SupportTable& table, const FarkasProfile& profile) const;

    // Enumerate up to `maxResults` satisfying assignments. Useful for
    // Phase 4 which validates each candidate against the original CoreIr;
    // the FIRST CSP-consistent assignment may still violate residual
    // outer assertions, so the caller iterates.
    std::vector<FarkasOrAssignment>
    enumerateCsp(const SupportTable& table, const FarkasProfile& profile,
                 std::size_t maxResults = 100) const;

    // Intersect [lo1, hi1] with [lo2, hi2] (any side may be infinite).
    // Public so the anonymous-namespace helpers in the .cpp can call it.
    static bool intersectInterval(
        std::pair<mpq_class, mpq_class>& cur,
        std::pair<bool, bool>& curFinite,
        const std::pair<mpq_class, mpq_class>& other,
        const std::pair<bool, bool>& otherFinite);

private:
    const CoreIr& ir_;
    FarkasOrBranchSolver p1_;
};

} // namespace xolver::farkas
