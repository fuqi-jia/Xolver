#include "search/refute/PresolveProjectionRefutation.h"
#include "search/presolve/PresolveProjection.h"
#include "search/refute/PolynomialLinearRefutation.h"
#include "search/refute/PolynomialSignClosure.h"
#include "search/refute/PolynomialConeRefutation.h"
#include "base/RuntimeConfig.h"
#include "base/SolveClock.h"
#include <algorithm>
#include <fstream>
#include <limits>

namespace xolver {
std::optional<std::vector<SatLit>> refutePresolveProjection(
    const PresolveProjection& projection, PolynomialKernel& kernel,
    PolynomialLinearRefuter& linear, PolynomialDomain domain) {
    if (projection.premises().empty()) return std::nullopt;
    std::vector<SignRefuteConstraint> constraints;
    for (const auto& source : projection.constraints()) {
        const auto polynomial = RationalPolynomial::fromPolyId(source.poly, kernel);
        if (!polynomial) return std::nullopt;
        if (constraints.size() >= std::numeric_limits<SatVar>::max()) return std::nullopt;
        // Distinct local labels preserve the identity of each reduced premise.
        // Reusing one original literal for several reduced rows loses that map.
        const auto reason = SatLit::positive(static_cast<SatVar>(constraints.size() + 1));
        constraints.push_back({*polynomial, source.rel, reason});
    }
    if (constraints.empty()) return std::nullopt;
    PolynomialLinearStatistics linearStats;
    PolynomialSignStatistics signStats;
    QuadraticSignStatistics quadraticStats;
    auto conflict = refuteBySignDefiniteness(constraints);
    if (!conflict) conflict = linear.check(constraints, wall::deadline(), &linearStats);
    std::vector<PolynomialConsequence> consequences;
    if (!conflict)
        conflict = refuteByPolynomialSignClosure(constraints, &signStats, domain, &consequences);
    if (!conflict) conflict = refuteByPolynomialCone(constraints, wall::deadline(), domain);
    if (!conflict && !consequences.empty())
        conflict = refuteByPolynomialConsequences(linear, constraints, consequences, wall::deadline());
    if (!conflict) conflict = refuteByQuadraticSigns(constraints, &quadraticStats);
    std::vector<SatLit> lifted;
    if (conflict) {
        for (const auto local : *conflict) {
            if (!local.sign || local.var == 0 || local.var > projection.constraints().size())
                return std::nullopt;
            const auto& reasons = projection.constraints()[local.var - 1].premises;
            lifted.insert(lifted.end(), reasons.begin(), reasons.end());
        }
        std::sort(lifted.begin(), lifted.end(), [](SatLit a, SatLit b) {
            return a.var != b.var ? a.var < b.var : a.sign < b.sign;
        });
        lifted.erase(std::unique(lifted.begin(), lifted.end()), lifted.end());
        if (lifted.empty()) return std::nullopt;
    }
    const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    if (!profile.empty()) {
        std::ofstream out(profile.string() + ".projected-refutation.log", std::ios::app);
        out << "integer=" << domain.allInteger << " constraints=" << constraints.size()
            << " variables=" << projection.variables().size()
            << " definitions=" << projection.definitionCount()
            << " linear_exhausted=" << linearStats.exhausted
            << " sign_exhausted=" << signStats.exhausted
            << " quadratic_certified=" << quadraticStats.certified
            << " conflict=" << bool(conflict) << " premises=" << lifted.size()
            << " original_premises=" << projection.premises().size() << '\n';
    }
    if (conflict) return lifted;
    return std::nullopt;
}
} // namespace xolver
