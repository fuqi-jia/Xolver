#include "theory/arith/logics/nia/farkas/FarkasOrModelAssembler.h"

#include <functional>

namespace xolver::farkas {

namespace {
mpz_class toIntFloor(const mpq_class& q) {
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();
    // num / den toward floor for positive denom (mpq normalizes denom > 0).
    if (num >= 0) {
        return num / den;
    }
    mpz_class r;
    mpz_class q_floor = (num - den + 1) / den;
    return q_floor;
}
mpz_class toIntCeil(const mpq_class& q) {
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();
    if (num <= 0) {
        return num / den;
    }
    return (num + den - 1) / den;
}
} // namespace

std::unordered_set<std::string>
FarkasOrModelAssembler::collectFreeVars(const FarkasProfile& profile) const {
    std::unordered_set<std::string> out;
    std::function<void(ExprId)> walk;
    walk = [&](ExprId id) {
        const auto& e = ir_.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) out.insert(*s);
            return;
        }
        for (ExprId c : e.children) walk(c);
    };
    for (ExprId aid : profile.outerAssertions) walk(aid);
    for (const auto& blk : profile.blocks) {
        for (const auto& br : blk.branches) {
            for (ExprId atom : br.equalities)   walk(atom);
            for (ExprId atom : br.inequalities) walk(atom);
        }
    }
    // ALSO walk ALL CoreIr assertions — the validator evaluates over the
    // original assertion list (which includes Tseitin `(= boolpur_K …)`
    // proxies + assertions that the detector consumed). Any variable used
    // in any assertion needs a value in M or the validator will see it as
    // unconstrained-but-referenced.
    for (ExprId aid : ir_.assertions()) walk(aid);
    return out;
}

std::optional<IntegerModel>
FarkasOrModelAssembler::assemble(const FarkasProfile& profile,
                                 const FarkasOrAssignment& assignment) const
{
    IntegerModel M;

    // 1. Bounded globals from the CSP B.
    for (const auto& [v, val] : assignment.B) {
        M[v] = val;
    }

    // 2. λ vars from per-block rays.
    for (const auto& [blockIdx, ray] : assignment.rayPerBlock) {
        auto it = assignment.lambdaNamesPerBlock.find(blockIdx);
        if (it == assignment.lambdaNamesPerBlock.end()) continue;
        const auto& names = it->second;
        if (names.size() != ray.size()) continue;
        for (std::size_t i = 0; i < names.size(); ++i) {
            M[names[i]] = ray[i];
        }
    }

    // 3. CT-like vars: pick a concrete integer inside the interval.
    //    Preference: the lower bound (if finite), else 0, else upper bound.
    for (const auto& [ctVar, ival] : assignment.ctInterval) {
        auto fit = assignment.ctFinite.find(ctVar);
        bool loFinite = fit != assignment.ctFinite.end() && fit->second.first;
        bool hiFinite = fit != assignment.ctFinite.end() && fit->second.second;
        if (loFinite && hiFinite && ival.first > ival.second) {
            // Empty interval after CSP — fail.
            return std::nullopt;
        }
        mpz_class pick;
        if (loFinite) {
            pick = toIntCeil(ival.first);
        } else if (hiFinite) {
            pick = toIntFloor(ival.second);
        } else {
            pick = 0;
        }
        // Clamp into [lo, hi] if both finite.
        if (loFinite) {
            mpz_class loCeil = toIntCeil(ival.first);
            if (pick < loCeil) pick = loCeil;
        }
        if (hiFinite) {
            mpz_class hiFloor = toIntFloor(ival.second);
            if (pick > hiFloor) pick = hiFloor;
        }
        M[ctVar] = pick;
    }

    // 3b. Residual co-vars committed by each block's chosen branch (RFN1_*
    //     in Stroeder). Apply BEFORE defaulting to 0 so these values stick.
    for (const auto& [blockIdx, residMap] : assignment.residPerBlock) {
        (void)blockIdx;
        for (const auto& [v, val] : residMap) {
            M[v] = val;
        }
    }

    // 3c. Boolean-Purification proxies (boolpur_K). For each Farkas block,
    //     the detector substituted Or children that were `boolpur_K`
    //     proxies with their `(and ...)` definitions. The original
    //     `(= boolpur_K (and ...))` Eq remains in the formula, so the
    //     validator demands proxy = eval(and ...). For the CHOSEN branch
    //     the and-body evaluates true → proxy = 1; for all others, the
    //     and-body may evaluate to either truth — we set proxy = 0 by
    //     default. Without this the validator fails to confirm SAT even
    //     when the underlying Farkas certificate is correct.
    for (std::size_t j = 0; j < profile.blocks.size(); ++j) {
        const auto& blk = profile.blocks[j];
        auto cit = assignment.choice.find((int)j);
        int chosen = (cit != assignment.choice.end()) ? cit->second : -1;
        for (std::size_t k = 0; k < blk.branchProxies.size(); ++k) {
            const auto& proxy = blk.branchProxies[k];
            if (proxy.empty()) continue;
            M[proxy] = ((int)k == chosen) ? mpz_class(1) : mpz_class(0);
        }
    }

    // 4. Residual vars: every Variable referenced in the formula but not yet
    //    assigned. Default to 0 (best effort).
    auto allVars = collectFreeVars(profile);
    for (const auto& v : allVars) {
        if (M.find(v) == M.end()) M[v] = 0;
    }

    return M;
}

} // namespace xolver::farkas
