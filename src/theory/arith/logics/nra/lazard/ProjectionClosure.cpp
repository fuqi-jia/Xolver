#include "theory/arith/logics/nra/lazard/ProjectionClosure.h"

#include <algorithm>
#include <utility>

namespace xolver {

namespace {
// Canonical string key for dedup (matches LocalProjection's scheme).
std::string polyKey(const RationalPolynomial& p) {
    std::string key;
    for (const auto& [mon, coeff] : p.terms()) {
        key += coeff.get_str() + ":";
        for (const auto& [v, e] : mon) {
            key += std::to_string(v) + "^" + std::to_string(e) + ";";
        }
        key += "|";
    }
    return key;
}
} // namespace

int ProjectionClosure::mainVarLevelOf(const RationalPolynomial& p) const {
    return p.highestVariableLevel(varOrder_);
}

const std::vector<int>& ProjectionClosure::levelPolys(int k) const {
    if (k < 0 || k >= static_cast<int>(levelPolys_.size())) return emptyLevel_;
    return levelPolys_[k];
}

int ProjectionClosure::intern(const RationalPolynomial& pIn,
                              const ProjectionSource& src) {
    RationalPolynomial p = pIn;
    p.normalize();
    if (p.isZero() || p.isConstant()) return -1;   // not a boundary polynomial
    // Canonicalize up to a rational unit: divide by the coefficient of the
    // largest monomial (map is sorted, so terms().rbegin() is stable). This
    // makes proportional polynomials — e.g. a coefficient y^2-x and a
    // discriminant -4(y^2-x) — collapse to ONE entry, so their pairwise
    // resultant is never (spuriously) zero and misread as a common factor.
    {
        mpq_class lead = p.terms().rbegin()->second;
        if (lead != 0 && lead != 1) {
            p *= (mpq_class(1) / lead);
            p.normalize();
        }
    }
    std::string key = polyKey(p);
    int id;
    auto it = dedup_.find(key);
    if (it != dedup_.end()) {
        id = it->second;
    } else {
        id = static_cast<int>(entries_.size());
        Entry e;
        e.mainVarLevel = mainVarLevelOf(p);
        e.poly = std::move(p);
        e.source = src;
        entries_.push_back(std::move(e));
        dedup_.emplace(std::move(key), id);
        if (entries_[id].mainVarLevel >= 0) {
            levelPolys_[entries_[id].mainVarLevel].push_back(id);
        }
    }
    // Feature A provenance: a derived op inherits the UNION of its parents' input
    // origins (run on dedup hits too, so an entry reachable by several derivations
    // accumulates all of them — the safe over-inclusive direction). Input origins
    // are added by build() (it knows the constraint index).
    if (static_cast<int>(entryInputs_.size()) <= id) entryInputs_.resize(id + 1);
    if (src.op != ProjectionOpKind::Input) {
        auto addOrigins = [&](int parent) {
            if (parent < 0 || parent >= static_cast<int>(entryInputs_.size())) return;
            std::vector<int>& dst = entryInputs_[id];
            for (int x : entryInputs_[parent])
                if (std::find(dst.begin(), dst.end(), x) == dst.end()) dst.push_back(x);
        };
        addOrigins(src.parent1);
        addOrigins(src.parent2);
    }
    return id;
}

void ProjectionClosure::projectLevel(const std::vector<int>& inputIds,
                                     VarId elimVar, int /*elimLevel*/) {
    // Per-polynomial: coefficients + PSC chain of (f, f').
    for (int id : inputIds) {
        const RationalPolynomial f = entries_[id].poly;  // copy (entries_ grows)

        auto coeffs = f.coefficients(elimVar);
        for (size_t i = 0; i < coeffs.size(); ++i) {
            ProjectionSource s;
            s.op = ProjectionOpKind::Coefficient;
            s.parent1 = id;
            s.eliminatedVar = elimVar;
            s.coeffIndex = static_cast<int>(i);
            intern(coeffs[i], s);   // intern skips zero/constant
        }

        RationalPolynomial fp = f.derivative(elimVar);
        if (!fp.isZero()) {
            auto chain = principalSubresultantCoefficients(f, fp, elimVar, cfg_.maxMatrixDim, kernel_);
            if (chain.budgetExceeded) { reason_ = ProjectionIncompleteReason::BudgetExceeded; return; }
            for (size_t j = 0; j < chain.psc.size(); ++j) {
                RationalPolynomial s = chain.psc[j];
                s.normalize();
                if (s.isZero()) {
                    // Repeated factor: its root is a root of f, already a
                    // boundary in the closure — skip (do not bail).
                    continue;
                }
                ProjectionSource src;
                src.op = ProjectionOpKind::PrincipalSubresultantCoefficient;
                src.parent1 = id; src.parent2 = id;
                src.eliminatedVar = elimVar; src.pscIndex = static_cast<int>(j);
                intern(s, src);
                if (entries_.size() > cfg_.maxPolys) { reason_ = ProjectionIncompleteReason::BudgetExceeded; return; }
            }
        }
    }

    // Pairwise: PSC chain of (f, g).
    for (size_t a = 0; a < inputIds.size(); ++a) {
        for (size_t b = a + 1; b < inputIds.size(); ++b) {
            const RationalPolynomial f = entries_[inputIds[a]].poly;
            const RationalPolynomial g = entries_[inputIds[b]].poly;
            auto chain = principalSubresultantCoefficients(f, g, elimVar, cfg_.maxMatrixDim, kernel_);
            if (chain.budgetExceeded) { reason_ = ProjectionIncompleteReason::BudgetExceeded; return; }
            for (size_t j = 0; j < chain.psc.size(); ++j) {
                RationalPolynomial s = chain.psc[j];
                s.normalize();
                if (s.isZero()) {
                    // Common factor between f and g: its roots are roots of f
                    // (and g), already boundaries in the closure — skip, do not
                    // bail. (Cross-checked by false-UNSAT = 0.)
                    continue;
                }
                ProjectionSource src;
                src.op = ProjectionOpKind::PrincipalSubresultantCoefficient;
                src.parent1 = inputIds[a]; src.parent2 = inputIds[b];
                src.eliminatedVar = elimVar; src.pscIndex = static_cast<int>(j);
                intern(s, src);
                if (entries_.size() > cfg_.maxPolys) { reason_ = ProjectionIncompleteReason::BudgetExceeded; return; }
            }
        }
    }
}

ProjectionIncompleteReason ProjectionClosure::build(
    const std::vector<RationalPolynomial>& constraints,
    const std::vector<VarId>& varOrder,
    const Config& cfg,
    PolynomialKernel* kernel) {

    entries_.clear();
    entryInputs_.clear();   // Feature A: per-entry input-constraint origin sets
    dedup_.clear();
    varOrder_ = varOrder;
    cfg_ = cfg;
    kernel_ = kernel;
    reason_ = ProjectionIncompleteReason::None;
    int n = static_cast<int>(varOrder.size());
    levelPolys_.assign(static_cast<size_t>(std::max(0, n)), {});

    for (size_t i = 0; i < constraints.size(); ++i) {
        ProjectionSource s; s.op = ProjectionOpKind::Input;
        const int id = intern(constraints[i], s);
        if (id < 0) continue;   // constant/zero — not a boundary
        // Record this input's origin index on the interned entry (dedup of two
        // identical input polys accumulates both indices — safe over-inclusion).
        if (static_cast<int>(entryInputs_.size()) <= id) entryInputs_.resize(id + 1);
        std::vector<int>& dst = entryInputs_[id];
        if (std::find(dst.begin(), dst.end(), static_cast<int>(i)) == dst.end())
            dst.push_back(static_cast<int>(i));
    }

    // Eliminate from the top variable down. Polys whose main variable is
    // varOrder[j] are projected at step j; their outputs (lower main var) are
    // interned and picked up at later (lower-j) steps — the chaining that the
    // single-step legacy projection lacked.
    for (int j = n - 1; j >= 1; --j) {
        std::vector<int> E = levelPolys_[j];   // snapshot (projection only adds lower levels)
        if (E.empty()) continue;
        projectLevel(E, varOrder[j], j);
        if (reason_ != ProjectionIncompleteReason::None) return reason_;
        if (entries_.size() > cfg_.maxPolys) { reason_ = ProjectionIncompleteReason::BudgetExceeded; return reason_; }
    }
    return reason_;
}

} // namespace xolver
