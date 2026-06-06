#include "theory/arith/nia/reasoners/ModEqConstReasoner.h"

#include <variant>

namespace xolver {

ModEqConstReasoner::ModEqConstReasoner(PolynomialKernel& kernel, const CoreIr& ir)
    : kernel_(kernel), ir_(ir) {}

std::string ModEqConstReasoner::varNameOf(ExprId eid) const {
    if (eid == NullExpr) return {};
    const auto& e = ir_.get(eid);
    if (e.kind != Kind::Variable) return {};
    if (auto* s = std::get_if<std::string>(&e.payload.value)) return *s;
    return {};
}

NiaReasoningResult ModEqConstReasoner::run(const ModEqConstFactList& facts,
                                            DomainStore& domains) {
    if (facts.empty()) {
        return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
    }

    bool anyDomainUpdated = false;
    for (const auto& fact : facts) {
        auto r = checkFact(fact, domains);
        if (r.kind == NiaReasoningKind::Conflict) return r;
        if (r.kind == NiaReasoningKind::DomainUpdated) anyDomainUpdated = true;
    }

    if (anyDomainUpdated) {
        return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

NiaReasoningResult ModEqConstReasoner::checkFact(const ModEqConstFact& fact,
                                                  DomainStore& domains) {
    const NiaReasoningResult noChange{NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // Phase 1.2 restricts to Variable y. Other shapes fall back to legacy q*y.
    std::string yName = varNameOf(fact.yExpr);
    if (yName.empty()) return noChange;

    const IntDomain* d = domains.getDomain(yName);
    if (!d) return noChange;  // y has no recorded domain — nothing to derive

    SatLit factLit = fact.reason;  // assumed populated by NiaSolver wiring

    // Rule 1: SMT-LIB Int mod always yields c in [0, |y|). If c < 0 and y
    //         is provably non-zero, the fact is unsatisfiable on the active
    //         branch (the EUF mod0 branch would still cover y=0; under pure
    //         NIA we have no mod0 routing, so the fact is refuted).
    if (fact.c < 0) {
        bool yNonZero = false;
        std::vector<SatLit> nzReasons;
        if (d->hasLower && d->lower.value > 0) {
            yNonZero = true;
            nzReasons = d->lower.reasons;
        } else if (d->hasUpper && d->upper.value < 0) {
            yNonZero = true;
            nzReasons = d->upper.reasons;
        }
        if (yNonZero) {
            TheoryConflict tc;
            tc.clause.push_back(factLit);
            for (auto l : nzReasons) tc.clause.push_back(l);
            return {NiaReasoningKind::Conflict, tc, std::nullopt};
        }
        return noChange;
    }

    // Rule 2: y > 0 provable → require y >= c+1.
    //   - if upper < c+1: Conflict (no value in [lower..upper] satisfies y>=c+1)
    //   - if existing lower < c+1: narrow lower to c+1
    if (d->hasLower && d->lower.value > 0) {
        mpz_class need = fact.c + 1;
        if (d->hasUpper && d->upper.value < need) {
            TheoryConflict tc;
            tc.clause.push_back(factLit);
            for (auto l : d->lower.reasons) tc.clause.push_back(l);
            for (auto l : d->upper.reasons) tc.clause.push_back(l);
            return {NiaReasoningKind::Conflict, tc, std::nullopt};
        }
        if (!d->hasLower || d->lower.value < need) {
            std::vector<SatLit> rs;
            rs.push_back(factLit);
            for (auto l : d->lower.reasons) rs.push_back(l);
            domains.addLowerBound(yName, need, rs);
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }
        return noChange;
    }

    // Rule 3: y < 0 provable → require y <= -c-1.
    //   - if lower > -c-1: Conflict
    //   - if existing upper > -c-1: narrow upper
    if (d->hasUpper && d->upper.value < 0) {
        mpz_class need = -(fact.c + 1);
        if (d->hasLower && d->lower.value > need) {
            TheoryConflict tc;
            tc.clause.push_back(factLit);
            for (auto l : d->lower.reasons) tc.clause.push_back(l);
            for (auto l : d->upper.reasons) tc.clause.push_back(l);
            return {NiaReasoningKind::Conflict, tc, std::nullopt};
        }
        if (!d->hasUpper || d->upper.value > need) {
            std::vector<SatLit> rs;
            rs.push_back(factLit);
            for (auto l : d->upper.reasons) rs.push_back(l);
            domains.addUpperBound(yName, need, rs);
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }
        return noChange;
    }

    return noChange;
}

}  // namespace xolver
