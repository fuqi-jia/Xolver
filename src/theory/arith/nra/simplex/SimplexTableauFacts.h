#pragma once
#include "theory/arith/nra/simplex/NraLinearExtractor.h"
#include "expr/types.h"
#include <unordered_map>
#include <optional>
#include <utility>
#include <vector>
#include <gmpxx.h>

namespace zolver {

// One non-basic term of a basic variable's row, with that term variable's
// currently stored bounds (nullopt = unbounded on that side).
struct RowTermBound { mpq_class coeff; std::optional<mpq_class> lo, hi; };

// Pure interval arithmetic for one solved-tableau row: xb = rhs + Σ coeff·col.
// Returns (lower, upper); a side is nullopt if any required col bound is missing.
std::pair<std::optional<mpq_class>, std::optional<mpq_class>>
deriveBasicInterval(const mpq_class& rhs, const std::vector<RowTermBound>& terms);

// Read-only facts from a SOLVED (SAT) fresh GeneralSimplex over the linear
// subset. Heuristic input to CDCAC variable ordering ONLY — never used for
// pruning, conflicts, or verdicts. On UNSAT: linearSubsetUnsat() == true and
// no ordering facts are populated (no conflict is produced).
class SimplexTableauFacts {
public:
    bool linearSubsetUnsat() const { return unsat_; }

    bool hasLower(VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.lo.has_value(); }
    bool hasUpper(VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.hi.has_value(); }
    bool isFixed (VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.lo && it->second.hi && *it->second.lo==*it->second.hi; }
    bool isBasic (VarId v) const { auto it=m_.find(v); return it!=m_.end() && it->second.basic; }
    int  boundedness(VarId v) const { return (hasLower(v)?1:0)+(hasUpper(v)?1:0); }
    int  rowParticipation(VarId v) const { return get(rowPart_, v); }
    int  tightRowParticipation(VarId v) const { return get(tight_, v); }

    struct E { std::optional<mpq_class> lo, hi; bool basic=false; };
    std::unordered_map<VarId,E>   m_;
    std::unordered_map<VarId,int> rowPart_, tight_;
    bool unsat_ = false;

    void tightenLower(VarId v, const mpq_class& b){ auto&e=m_[v]; if(!e.lo||b>*e.lo) e.lo=b; }
    void tightenUpper(VarId v, const mpq_class& b){ auto&e=m_[v]; if(!e.hi||b<*e.hi) e.hi=b; }
private:
    static int get(const std::unordered_map<VarId,int>&m, VarId v){ auto it=m.find(v); return it==m.end()?0:it->second; }
};

SimplexTableauFacts computeSimplexTableauFacts(
    const PolynomialKernel& kernel,
    const std::vector<LinearAtom>& linear);

} // namespace zolver
