#include "theory/arith/nra/search/HybridPartitionStats.h"
#include <cstdio>
#include <cstdlib>
#include <unordered_set>

namespace xolver {

HybridPartitionReport computePartition(
    const std::vector<PolyId>& polys,
    PolynomialKernel& kernel) {

    HybridPartitionReport r;
    r.totalConstraints = static_cast<uint32_t>(polys.size());

    std::unordered_set<VarId> linearVars;     // vars appearing in any linear constraint
    std::unordered_set<VarId> nonlinearVars;  // vars appearing in any nonlinear constraint
    std::unordered_set<VarId> allVars;

    for (PolyId p : polys) {
        if (p == NullPoly) continue;
        auto termsOpt = kernel.terms(p);  // S1c cached
        if (!termsOpt) {
            // Decomposition failed: conservatively treat as nonlinear and
            // include all variables() of the poly.
            ++r.nonlinearConstraints;
            for (const auto& vn : kernel.variables(p)) {  // S1d cached
                auto vid = kernel.findVar(vn);
                if (vid) {
                    nonlinearVars.insert(*vid);
                    allVars.insert(*vid);
                }
            }
            continue;
        }
        bool isLinear = true;
        std::unordered_set<VarId> cVars;
        for (const auto& term : *termsOpt) {
            int totalDeg = 0;
            for (const auto& [vid, exp] : term.powers) {
                cVars.insert(vid);
                totalDeg += exp;
            }
            if (totalDeg > 1) isLinear = false;
        }
        if (isLinear) {
            ++r.linearConstraints;
            for (VarId v : cVars) { linearVars.insert(v); allVars.insert(v); }
        } else {
            ++r.nonlinearConstraints;
            for (VarId v : cVars) { nonlinearVars.insert(v); allVars.insert(v); }
        }
    }

    r.totalVars = static_cast<uint32_t>(allVars.size());
    for (VarId v : allVars) {
        const bool inL = linearVars.count(v) > 0;
        const bool inN = nonlinearVars.count(v) > 0;
        if (inL && inN) ++r.mixedVars;
        else if (inL)   ++r.pureLinearVars;
        else if (inN)   ++r.pureNonlinearVars;
        // (a var with neither cannot happen — it was added via inL or inN)
    }
    return r;
}

void maybeDumpPartitionReport(const HybridPartitionReport& report) {
    if (!std::getenv("XOLVER_NRA_HYB_PARTITION_STATS")) return;
    std::fprintf(stderr,
        "[XOLVER_NRA_HYB_PARTITION_STATS] constraints L=%u N=%u total=%u "
        "linear_frac=%.2f%% | vars V_L=%u V_N=%u V_M=%u total=%u "
        "mixed_frac=%.2f%%\n",
        report.linearConstraints, report.nonlinearConstraints,
        report.totalConstraints,
        100.0 * report.linearConstraintFraction(),
        report.pureLinearVars, report.pureNonlinearVars, report.mixedVars,
        report.totalVars,
        100.0 * report.mixedVarFraction());
}

} // namespace xolver
