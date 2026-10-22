#include "base/RuntimeConfig.h"
#include "search/presolve/Presolve.h"
#include "base/EnvParam.h"
#include "search/presolve/AffineSubstitution.h"
#include "search/presolve/IntLinearEqualityCoreHNF.h"
#include "search/presolve/PolynomialEqualityCombination.h"
#include "search/presolve/PolynomialDefSubstitution.h"
#include "search/presolve/NonnegativePolynomialBoundExtractor.h"
#include "search/presolve/BoundChainComposer.h"
#include "search/presolve/UnivariatePolySignAnalyzer.h"
#include <cstdlib>
#include <iostream>
#include <set>

namespace xolver {

// XOLVER_PRESOLVE_DIAG: print the firing capability + conflicting atoms at the
// conflict-emission point. Diagnosis only (default-off).
static void dumpPresolveConflict(const char* cap, const PresolveState& st) {
    auto polySummary = [](const RationalPolynomial& p) -> std::string {
        if (p.isConstant()) return "const=" + p.constantValue().get_str();
        std::string s;
        bool first = true;
        for (const auto& e : p.terms()) {
            if (!first) s += " + ";
            first = false;
            s += e.second.get_str();
            for (const auto& vp : e.first) s += "*x" + std::to_string(vp.first) +
                                               (vp.second != 1 ? "^" + std::to_string(vp.second) : "");
        }
        return s.empty() ? "0" : s;
    };
    auto relStr = [](Relation r) {
        switch (r) { case Relation::Eq: return "=0"; case Relation::Neq: return "!=0";
            case Relation::Lt: return "<0"; case Relation::Leq: return "<=0";
            case Relation::Gt: return ">0"; case Relation::Geq: return ">=0"; }
        return "?";
    };
    std::cerr << "[PRESOLVE-DIAG] firing-cap=" << cap
              << " conflict-clause(" << st.conflict.clause.size() << ")=";
    std::set<int> conflictVars;
    for (auto l : st.conflict.clause) { std::cerr << (l.sign ? "" : "-") << l.var << " "; conflictVars.insert(l.var); }
    std::cerr << "\n";
    for (const auto& a : st.atoms) {
        if (!a.live) continue;
        bool inConflict = false;
        for (auto l : a.reasons.baseLiterals) if (conflictVars.count(l.var)) inConflict = true;
        std::cerr << "  " << (inConflict ? "* " : "  ") << polySummary(a.poly) << " " << relStr(a.rel)
                  << "  lits=";
        for (auto l : a.reasons.baseLiterals) std::cerr << (l.sign ? "" : "-") << l.var << " ";
        std::cerr << "\n";
    }
}

PresolveEngine::PresolveEngine(PolynomialKernel* kernel, bool integerDomain) {
    st_.kernel = kernel;
    st_.integerDomain = integerDomain;

    // Analyze the original univariate constraints before substitutions can
    // turn them into multivariate ones. Derived univariate constraints are
    // analyzed on the next fixpoint sweep, with the same memoized capability.
    caps_.push_back(std::make_unique<UnivariatePolySignAnalyzer>());
    caps_.push_back(std::make_unique<IntLinearEqualityCoreHNF>());    // Cap. 5 (Int)
    caps_.push_back(std::make_unique<PolynomialEqualityCombination>()); // Cap. 3
    caps_.push_back(std::make_unique<AffineSubstitution>());          // Cap. 1
    caps_.push_back(std::make_unique<PolynomialDefSubstitution>());        // Cap. 2
    caps_.push_back(std::make_unique<NonnegativePolynomialBoundExtractor>()); // Cap. 11
    caps_.push_back(std::make_unique<BoundChainComposer>());               // Cap. 7
}

void PresolveEngine::addAtom(const RationalPolynomial& poly, Relation rel, SatLit reason) {
    PresolveAtom a;
    a.poly = poly;
    a.poly.normalize();
    a.rel = rel;
    a.reasons.baseLiterals.push_back(reason);
    a.live = true;
    st_.atoms.push_back(std::move(a));
}

PresolveResult PresolveEngine::run(std::chrono::steady_clock::time_point deadline) {
    st_.deadline = deadline;
    bool anyProgress = false;
    int sweeps = 0;
    const bool haveDeadline =
        deadline != std::chrono::steady_clock::time_point::max();
    auto pastDeadline = [&]() {
        return haveDeadline && std::chrono::steady_clock::now() >= deadline;
    };
    while (true) {
        bool progress = false;
        for (auto& cap : caps_) {
            if (pastDeadline()) {
                PresolveResult r;
                r.kind = anyProgress ? PresolveResult::Kind::Progress
                                     : PresolveResult::Kind::NoProgress;
                return r;
            }
            if (cap->run(st_)) { progress = true; anyProgress = true; }
            if (st_.hasConflict) {
                if (xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_PRESOLVE_DIAG")) dumpPresolveConflict(cap->name(), st_);
                PresolveResult r;
                r.kind = PresolveResult::Kind::Conflict;
                r.conflict = st_.conflict;
                return r;
            }
            if (st_.hasLemma) {
                PresolveResult r;
                r.kind = PresolveResult::Kind::Lemma;
                r.lemma = st_.lemma;
                return r;
            }
            // Iter#21 deadline check (per-capability granularity). SOUND:
            // any Conflict / Lemma terminations already returned via the
            // branches above. Returning here exits with the partial fact
            // set in st_.ledger; downstream stages see only the derivations
            // that completed within budget — never a wrong claim.
            if (pastDeadline()) {
                PresolveResult r;
                r.kind = anyProgress ? PresolveResult::Kind::Progress
                                     : PresolveResult::Kind::NoProgress;
                return r;
            }
        }
        if (!progress) break;
        if (++sweeps >= kMaxFactsPerSweep) break;
        if (st_.ledger.size() >= static_cast<size_t>(kMaxFactsPerSweep)) break;
    }
    PresolveResult r;
    r.kind = anyProgress ? PresolveResult::Kind::Progress : PresolveResult::Kind::NoProgress;
    return r;
}

} // namespace xolver
