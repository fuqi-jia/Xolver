#include "theory/arith/logics/nra/simplex/PolyStructureFacts.h"
#include <set>

namespace xolver {

namespace {
// A monomial of total degree d with v-exponent e becomes linear after fixing v
// iff d <= 1 (already linear) or (v present and d - e <= 1).
bool monomialLinearAfterFixing(const PolynomialKernel::MonomialTerm& t, VarId v) {
    int total = 0, ev = 0;
    for (const auto& pe : t.powers) { total += pe.second; if (pe.first == v) ev = pe.second; }
    if (total <= 1) return true;
    if (ev == 0) return false;
    return (total - ev) <= 1;
}
} // namespace

PolyStructureFacts computeStructureFacts(
    const PolynomialKernel& kernel,
    const std::vector<CdcacConstraint>& nonlinearConstraints) {
    PolyStructureFacts f;
    for (const auto& c : nonlinearConstraints) {
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;

        bool hasNonlinearMon = false;
        std::set<VarId> varsInC;
        for (const auto& t : *termsOpt) {
            int total = 0;
            for (const auto& pe : t.powers) total += pe.second;
            bool nl = (total >= 2);
            if (nl) hasNonlinearMon = true;
            for (const auto& pe : t.powers) {
                VarId v = pe.first;
                varsInC.insert(v);
                if (pe.second > f.maxDeg_[v]) f.maxDeg_[v] = pe.second;
                if (nl) ++f.connect_[v];
            }
        }
        if (!hasNonlinearMon) continue;

        for (VarId v : varsInC) {
            bool all = true;
            for (const auto& t : *termsOpt)
                if (!monomialLinearAfterFixing(t, v)) { all = false; break; }
            if (all) ++f.linGain_[v];
        }
    }
    return f;
}

} // namespace xolver
