#include "theory/arith/logics/nia/reasoners/ModEqConstReasoner.h"

#include <variant>

namespace xolver {

ModEqConstReasoner::ModEqConstReasoner(PolynomialKernel& kernel, const CoreIr* ir)
    : kernel_(kernel), ir_(ir) {}

std::string ModEqConstReasoner::varNameOf(ExprId eid) const {
    if (!ir_ || eid == NullExpr) return {};
    const auto& e = ir_->get(eid);
    if (e.kind != Kind::Variable) return {};
    if (auto* s = std::get_if<std::string>(&e.payload.value)) return *s;
    return {};
}

NiaReasoningResult ModEqConstReasoner::run(const ModEqConstFactList& facts,
                                            DomainStore& domains) {
    if (!ir_ || facts.empty()) {
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
        // No conflict, no narrowing — fall through to rules 4/7 below.
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
        // No conflict, no narrowing — fall through.
    }

    // Rule 7: constant divisor specialization (Phase 1.4). If y's domain is
    // pinned to a single non-zero value k, the SMT-LIB Int mod remainder
    // lies in [0,|k|). If c is outside that interval, the fact is refuted.
    if (d->hasLower && d->hasUpper && d->lower.value == d->upper.value &&
        d->lower.value != 0) {
        mpz_class k = d->lower.value;
        mpz_class absK = (k > 0 ? k : -k);
        if (fact.c < 0 || fact.c >= absK) {
            TheoryConflict tc;
            tc.clause.push_back(factLit);
            for (auto l : d->lower.reasons) tc.clause.push_back(l);
            for (auto l : d->upper.reasons) tc.clause.push_back(l);
            return {NiaReasoningKind::Conflict, tc, std::nullopt};
        }
        return noChange;
    }

    // Rule 4: large-divisor collapse (Phase 1.4). If min|y| > max|x-c| from
    // bounds and y excludes 0, then y*q = x-c with q integer forces q=0,
    // hence x = c. Restricted to Variable x.
    if (d->hasLower && d->hasUpper) {
        std::string xName = varNameOf(fact.xExpr);
        if (xName.empty()) return noChange;
        const IntDomain* dx = domains.getDomain(xName);
        if (!dx || !dx->hasLower || !dx->hasUpper) return noChange;

        bool yExcludesZero =
            (d->lower.value > 0) || (d->upper.value < 0);
        if (!yExcludesZero) return noChange;

        mpz_class minAbsY =
            (d->lower.value > 0) ? d->lower.value : -d->upper.value;
        mpz_class diffLo = dx->lower.value - fact.c;
        mpz_class diffUp = dx->upper.value - fact.c;
        mpz_class maxAbsDiff = (diffLo >= 0 ? diffLo : -diffLo);
        {
            mpz_class b = (diffUp >= 0 ? diffUp : -diffUp);
            if (b > maxAbsDiff) maxAbsDiff = b;
        }
        if (minAbsY <= maxAbsDiff) return noChange;

        // minAbsY > maxAbsDiff → x must equal c.
        if (fact.c < dx->lower.value || fact.c > dx->upper.value) {
            TheoryConflict tc;
            tc.clause.push_back(factLit);
            for (auto l : d->lower.reasons) tc.clause.push_back(l);
            for (auto l : d->upper.reasons) tc.clause.push_back(l);
            for (auto l : dx->lower.reasons) tc.clause.push_back(l);
            for (auto l : dx->upper.reasons) tc.clause.push_back(l);
            return {NiaReasoningKind::Conflict, tc, std::nullopt};
        }
        std::vector<SatLit> rs;
        rs.push_back(factLit);
        for (auto l : d->lower.reasons) rs.push_back(l);
        for (auto l : d->upper.reasons) rs.push_back(l);
        for (auto l : dx->lower.reasons) rs.push_back(l);
        for (auto l : dx->upper.reasons) rs.push_back(l);
        bool changed = false;
        if (!dx->hasLower || dx->lower.value < fact.c) {
            domains.addLowerBound(xName, fact.c, rs);
            changed = true;
        }
        if (!dx->hasUpper || dx->upper.value > fact.c) {
            domains.addUpperBound(xName, fact.c, rs);
            changed = true;
        }
        if (changed) {
            return {NiaReasoningKind::DomainUpdated, std::nullopt, std::nullopt};
        }
    }

    return noChange;
}

}  // namespace xolver
