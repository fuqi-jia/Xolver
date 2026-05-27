#include "theory/arith/nra/projection/LazardProjectionClosure.h"

#include <algorithm>
#include <utility>

namespace zolver {

namespace {
std::string polyKey(const RationalPolynomial& p) {
    std::string key;
    for (const auto& [mon, coeff] : p.terms()) {
        key += coeff.get_str() + ":";
        for (const auto& [v, e] : mon) key += std::to_string(v) + "^" + std::to_string(e) + ";";
        key += "|";
    }
    return key;
}
}  // namespace

// Normalize + canonicalize up to a rational unit (divide by the coefficient of
// the largest monomial). Matches ProjectionClosure::intern and Squarefree, so
// proportional polys (e.g. a coefficient and its discriminant multiple) collapse
// to one entry and their pairwise resultant is never spuriously zero.
std::string LazardProjectionClosure::canonicalKey(RationalPolynomial p) {
    p.normalize();
    if (p.isZero()) return std::string();
    mpq_class lead = p.terms().rbegin()->second;
    if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }
    return polyKey(p);
}

int LazardProjectionClosure::mainVarLevelOf(const RationalPolynomial& p) const {
    return p.highestVariableLevel(varOrder_);
}

const std::vector<int>& LazardProjectionClosure::levelPolys(int k) const {
    if (k < 0 || k >= static_cast<int>(levelPolys_.size())) return emptyLevel_;
    return levelPolys_[k];
}

int LazardProjectionClosure::lookupIndex(const RationalPolynomial& p) const {
    std::string key = canonicalKey(p);
    if (key.empty()) return -1;
    auto it = dedup_.find(key);
    return it == dedup_.end() ? -1 : it->second;
}

int LazardProjectionClosure::intern(const RationalPolynomial& pIn,
                                    const LazardProjectionSource& src) {
    RationalPolynomial p = pIn;
    p.normalize();
    if (p.isZero() || p.isConstant()) return -1;   // constants have no real-root boundary
    mpq_class lead = p.terms().rbegin()->second;
    if (lead != 0 && lead != 1) { p *= (mpq_class(1) / lead); p.normalize(); }

    std::string key = polyKey(p);
    auto it = dedup_.find(key);
    if (it != dedup_.end()) return it->second;

    int id = static_cast<int>(entries_.size());
    Entry e;
    e.mainVarLevel = mainVarLevelOf(p);
    e.poly = std::move(p);
    e.source = src;
    entries_.push_back(std::move(e));
    dedup_.emplace(std::move(key), id);
    if (entries_[id].mainVarLevel >= 0)
        levelPolys_[entries_[id].mainVarLevel].push_back(id);
    return id;
}

void LazardProjectionClosure::projectLevel(const std::vector<int>& inputIds, VarId elimVar) {
    std::vector<RationalPolynomial> E;
    E.reserve(inputIds.size());
    for (int id : inputIds) E.push_back(entries_[id].poly);

    LazardProjectionConfig opCfg;
    opCfg.maxMatrixDim = cfg_.maxMatrixDim;
    LazardOpResult op = lazardProjectStep(E, elimVar, opCfg, kernel_);
    if (!op.complete) { reason_ = op.reason; return; }

    // Items are emitted parents-before-dependents, so lookupIndex resolves each
    // parent (already interned) to its entry index.
    for (const auto& item : op.items) {
        LazardProjectionSource src;
        src.op = item.op;
        src.eliminatedVar = elimVar;
        src.parent1 = item.hasParent1 ? lookupIndex(item.parent1) : -1;
        src.parent2 = item.hasParent2 ? lookupIndex(item.parent2) : -1;
        intern(item.poly, src);
        if (entries_.size() > cfg_.maxPolys) {
            reason_ = LazardIncompleteReason::ProjectionBudgetExceeded;
            return;
        }
    }
}

LazardIncompleteReason LazardProjectionClosure::build(
    const std::vector<RationalPolynomial>& constraints,
    const std::vector<VarId>& varOrder, const Config& cfg,
    PolynomialKernel* kernel) {

    entries_.clear();
    dedup_.clear();
    varOrder_ = varOrder;
    cfg_ = cfg;
    kernel_ = kernel;
    reason_ = LazardIncompleteReason::None;
    int n = static_cast<int>(varOrder.size());
    levelPolys_.assign(static_cast<size_t>(std::max(0, n)), {});

    for (const auto& c : constraints) {
        LazardProjectionSource s;
        s.op = LazardProjectionOpKind::Input;
        intern(c, s);
    }

    // Eliminate from the top variable down; outputs (lower main var) are interned
    // and picked up at later (lower-j) steps.
    for (int j = n - 1; j >= 1; --j) {
        std::vector<int> E = levelPolys_[j];   // snapshot
        if (E.empty()) continue;
        projectLevel(E, varOrder[j]);
        if (reason_ != LazardIncompleteReason::None) return reason_;
        if (entries_.size() > cfg_.maxPolys) {
            reason_ = LazardIncompleteReason::ProjectionBudgetExceeded;
            return reason_;
        }
    }
    return reason_;
}

}  // namespace zolver
