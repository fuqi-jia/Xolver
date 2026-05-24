#include "theory/arith/presolve/Presolve.h"
#include "theory/arith/presolve/AffineSubstitution.h"
#include "theory/arith/presolve/IntLinearEqualityCoreHNF.h"
#include "theory/arith/presolve/PolynomialDefSubstitution.h"
#include "theory/arith/presolve/NonnegativePolynomialBoundExtractor.h"
#include "theory/arith/presolve/BoundChainComposer.h"
#include "theory/arith/presolve/UnivariatePolySignAnalyzer.h"

namespace nlcolver {

PresolveEngine::PresolveEngine(PolynomialKernel* kernel, bool integerDomain) {
    st_.kernel = kernel;
    st_.integerDomain = integerDomain;

    // Capability order (plan §Execution Pipeline, theory-check fixpoint):
    //   5 (linear cores) → 3 → 1 → 2 → 11 → 7 → 4 → 6.
    // Capabilities are appended as they are implemented; the fixpoint runs them
    // in this order until no new fact is derived.
    caps_.push_back(std::make_unique<IntLinearEqualityCoreHNF>());    // Cap. 5 (Int)
    caps_.push_back(std::make_unique<AffineSubstitution>());          // Cap. 1
    caps_.push_back(std::make_unique<PolynomialDefSubstitution>());        // Cap. 2
    caps_.push_back(std::make_unique<NonnegativePolynomialBoundExtractor>()); // Cap. 11
    caps_.push_back(std::make_unique<BoundChainComposer>());               // Cap. 7
    caps_.push_back(std::make_unique<UnivariatePolySignAnalyzer>());  // Cap. 4
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

PresolveResult PresolveEngine::run() {
    bool anyProgress = false;
    int sweeps = 0;
    while (true) {
        bool progress = false;
        for (auto& cap : caps_) {
            if (cap->run(st_)) { progress = true; anyProgress = true; }
            if (st_.hasConflict) {
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
        }
        if (!progress) break;
        if (++sweeps >= kMaxFactsPerSweep) break;
        if (st_.ledger.size() >= static_cast<size_t>(kMaxFactsPerSweep)) break;
    }
    PresolveResult r;
    r.kind = anyProgress ? PresolveResult::Kind::Progress : PresolveResult::Kind::NoProgress;
    return r;
}

} // namespace nlcolver
