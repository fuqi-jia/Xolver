#pragma once

#include "theory/arith/logics/nia/NiaTypes.h"
#include "theory/arith/logics/nia/preprocess/NiaNormalizer.h"
#include "theory/arith/logics/nia/core/DomainStore.h"
#include "theory/arith/kernel/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace xolver {

/**
 * VariablePartition (HYB-1, master 2026-06-02 8h independent).
 *
 * Foundation pass for the hybrid LS+BitBlast strategy. For every variable
 * appearing in a normalized constraint set, derive whether the variable is
 * BOUNDED (lower + upper both finite AND the resulting bit-width <= max)
 * or UNBOUNDED (one or both bounds missing, OR bit-width too large to
 * encode efficiently).
 *
 * The partition is purely informational — no constraint mutation. The
 * downstream hybrid solver consumes it to decide which vars get the
 * complete bit-blast treatment (B) and which stay in the local-search
 * domain (U). HYB-2 / HYB-3 / HYB-4 build on this.
 *
 * Two bound sources are combined (UNION):
 *   1. The DomainStore the caller passes in (already populated by
 *      upstream NIA reasoners: LinearNiaDomainReasoner, SquareBound,
 *      Domain inference).
 *   2. Direct scan of the constraint set for single-var bound atoms
 *      `±x + c rel 0` (a degree-1 coefficient of ±1 on a single var).
 *      This catches the bound atoms that haven't yet been DomainStore-
 *      installed at the call site (the partition may run before the
 *      domain reasoner has fully populated DomainStore in tests / early
 *      stages).
 *
 * Soundness: VariablePartition only READS constraint metadata; it makes
 * no claims about the formula's satisfiability. Misclassifying a var as
 * bounded vs unbounded only affects HYB strategy efficiency, never
 * verdict.
 */
struct VarPartitionInfo {
    bool hasLower = false;
    bool hasUpper = false;
    mpz_class lower = 0;
    mpz_class upper = 0;
    // The smallest signed bit-width that covers [lower, upper] (0 if
    // unbounded).
    unsigned bitWidth = 0;
    // True iff hasLower && hasUpper && bitWidth <= cap.
    bool isBounded = false;
};

struct PartitionResult {
    // var -> info
    std::unordered_map<std::string, VarPartitionInfo> info;

    // B = bounded (fits in bit-width cap); U = unbounded or oversized.
    std::unordered_set<std::string> bounded;
    std::unordered_set<std::string> unbounded;

    // Aggregate statistics (for the H5 diagnostic).
    size_t totalVars() const { return bounded.size() + unbounded.size(); }
    double averageBitWidthBounded() const;
    size_t unboundedCount() const { return unbounded.size(); }
    size_t boundedCount() const { return bounded.size(); }
    // Maximum bitwidth in the bounded set (informs HYB-2 BB sub-call sizing).
    unsigned maxBitWidthBounded() const;
};

class VariablePartition {
public:
    explicit VariablePartition(PolynomialKernel& kernel);

    // Compute partition on the given constraint set + bounds source.
    // maxBitWidth caps which vars qualify as "bounded enough" for BB.
    PartitionResult partition(
        const std::vector<NormalizedNiaConstraint>& constraints,
        const DomainStore& domains,
        unsigned maxBitWidth = 32) const;

private:
    PolynomialKernel& kernel_;

    // Smallest signed bit-width w with -2^(w-1) <= lo and hi <= 2^(w-1)-1.
    static unsigned bitsToCover(const mpz_class& lo, const mpz_class& hi);

    // Try to extract `coef*x + c rel 0` with coef = ±1 from a polynomial
    // (degree-1 single variable, linear coefficient ±1).
    bool extractSingleVarBound(PolyId poly, std::string& var,
                                int& coef, mpz_class& constTerm) const;
};

} // namespace xolver
