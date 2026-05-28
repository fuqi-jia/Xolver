#include "theory/arith/nia/reasoners/ModularResidueReasoner.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace xolver {

namespace {

using Term = PolynomialKernel::MonomialTerm;

bool isPow2(const mpz_class& v) {
    return v > 0 && mpz_popcount(v.get_mpz_t()) == 1;
}

// Reduce a into [0, m).
mpz_class modPos(const mpz_class& a, const mpz_class& m) {
    mpz_class r = a % m;
    if (r < 0) r += m;
    return r;
}

// ----- the derivation plan, built once per run -----

struct ModGroup {
    std::string rVar;         // remainder, derived: r = a mod n
    std::string qVar;         // quotient, eliminated via n*q = a - r
    mpz_class   n;            // power-of-two divisor
    PolyId      aPoly;        // dividend a (over earlier variables)
    SatLit      eqReason;
    SatLit      loReason;     // 0 <= r
    SatLit      hiReason;     // r <= n-1
};

struct SimpleDef {
    std::string vVar;
    PolyId      defPoly;      // v := defPoly (does not mention v)
    SatLit      reason;
};

struct CheckEq {
    PolyId poly;
    SatLit reason;
};

struct NeqC {
    PolyId poly;
    SatLit reason;
};

struct Bound {
    bool has = false;
    mpz_class val;
    SatLit reason{SatLit::positive(0)};
};

struct BoundPair { Bound lo, hi; };

} // namespace

ModularResidueReasoner::ModularResidueReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

namespace {

// Rebuild a PolyId from a subset of monomial terms.
PolyId buildFromTerms(PolynomialKernel& k, const std::vector<const Term*>& terms) {
    PolyId acc = k.mkZero();
    for (const Term* t : terms) {
        PolyId mono = k.mkConst(mpq_class(t->coefficient));
        for (const auto& [vid, exp] : t->powers) {
            mono = k.mul(mono, k.pow(k.mkVar(vid), static_cast<uint32_t>(exp)));
        }
        acc = k.add(acc, mono);
    }
    return acc;
}

// Parse a single-variable bound `coeff*v + c  rel  0` with coeff = ±1.
struct ParsedBound { std::string var; bool isUpper; mpz_class val; };
std::optional<ParsedBound> parseBound(PolynomialKernel& k, PolyId poly, Relation rel) {
    if (rel != Relation::Leq && rel != Relation::Geq) return std::nullopt;
    auto termsOpt = k.terms(poly);
    if (!termsOpt) return std::nullopt;
    mpz_class constVal = 0;
    const Term* varTerm = nullptr;
    for (const auto& t : *termsOpt) {
        if (t.powers.empty()) { constVal += t.coefficient; continue; }
        if (varTerm) return std::nullopt;                 // 2nd variable term
        if (t.powers.size() != 1 || t.powers[0].second != 1) return std::nullopt;
        if (t.coefficient != 1 && t.coefficient != -1) return std::nullopt;
        varTerm = &t;
    }
    if (!varTerm) return std::nullopt;
    mpz_class coeff = varTerm->coefficient;             // ±1
    mpz_class val = -constVal / coeff;                  // exact (coeff = ±1)
    bool coeffPos = coeff > 0;
    bool leq = (rel == Relation::Leq);
    // Leq,coeff>0 -> upper; Leq,coeff<0 -> lower; Geq,coeff>0 -> lower; Geq,coeff<0 -> upper
    bool isUpper = (leq == coeffPos);
    return ParsedBound{std::string(k.varName(varTerm->powers[0].first)), isUpper, val};
}

} // namespace

NiaReasoningResult ModularResidueReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints) {

    const NiaReasoningResult NO_CHANGE{NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // --- 1. Partition + collect single-variable bounds ---
    std::vector<size_t> eqIdx, neqIdx;
    std::unordered_map<std::string, BoundPair> bounds;
    for (size_t i = 0; i < constraints.size(); ++i) {
        const auto& c = constraints[i];
        if (c.rel == Relation::Eq) eqIdx.push_back(i);
        else if (c.rel == Relation::Neq) neqIdx.push_back(i);
        else if (auto pb = parseBound(kernel_, c.poly, c.rel)) {
            auto& bp = bounds[pb->var];
            Bound b; b.has = true; b.val = pb->val; b.reason = c.reason;
            if (pb->isUpper) { if (!bp.hi.has || pb->val < bp.hi.val) bp.hi = b; }
            else             { if (!bp.lo.has || pb->val > bp.lo.val) bp.lo = b; }
        }
    }
    if (eqIdx.empty()) return NO_CHANGE;

    // --- 2. Recognize div/mod groups (a = n*q + r, 0<=r<n) ---
    std::vector<ModGroup> groups;
    std::unordered_set<size_t> consumed;        // eq indices used as a group
    std::unordered_set<std::string> moddefVars; // r's
    std::unordered_set<std::string> quotientVars; // q's

    // 2a. Collect ALL candidate matches (eq, q, r, n, a) without claiming.
    //     An equation like `inv1 = 4*q2 + r5` (a *definition* of the real var
    //     inv1) is structurally indistinguishable from a div group
    //     `r5 = inv1 mod 4`; greedy first-match would mis-claim it and steal
    //     q2/r5 from their true defining equations. So we resolve globally:
    //     a remainder that is a candidate in exactly one equation is
    //     unambiguous; accepting those first claims their quotients, which then
    //     disambiguates the rest.
    struct Cand {
        size_t ei; std::string q, r; mpz_class n; PolyId aPoly;
        SatLit eqReason, loR, hiR;
    };
    std::vector<Cand> cands;
    for (size_t ei : eqIdx) {
        const auto& c = constraints[ei];
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        if (terms.size() < 2) continue;
        for (size_t qi = 0; qi < terms.size(); ++qi) {
            const Term& qt = terms[qi];
            if (qt.powers.size() != 1 || qt.powers[0].second != 1) continue;
            mpz_class n = abs(qt.coefficient);
            // Any modulus n >= 2 (not just powers of two): the quotient
            // elimination n*q = a - r and the remainder r = a mod n are exact
            // for any n, so the enumeration path generalizes to `mod 3/5/10/...`.
            // (The Hensel-lifting section stays pow2-only via log2pow2.)
            if (n < 2) continue;
            int eqSign = qt.coefficient > 0 ? 1 : -1;
            std::string qName = std::string(kernel_.varName(qt.powers[0].first));
            for (size_t ri = 0; ri < terms.size(); ++ri) {
                if (ri == qi) continue;
                const Term& rt = terms[ri];
                if (rt.powers.size() != 1 || rt.powers[0].second != 1) continue;
                if (rt.coefficient != 1 && rt.coefficient != -1) continue;
                if ((rt.coefficient > 0 ? 1 : -1) != eqSign) continue; // clean a = n*q + r
                std::string rName = std::string(kernel_.varName(rt.powers[0].first));
                if (rName == qName) continue;
                auto bit = bounds.find(rName);
                if (bit == bounds.end()) continue;
                if (!bit->second.lo.has || bit->second.lo.val != 0) continue;
                if (!bit->second.hi.has || bit->second.hi.val != n - 1) continue;
                std::vector<const Term*> rest;
                for (size_t k = 0; k < terms.size(); ++k)
                    if (k != qi && k != ri) rest.push_back(&terms[k]);
                PolyId leftover = buildFromTerms(kernel_, rest);
                PolyId aPoly = (eqSign == 1) ? kernel_.neg(leftover) : leftover;
                bool clean = true;
                for (const auto& v : kernel_.variables(aPoly))
                    if (v == rName || v == qName) { clean = false; break; }
                if (!clean) continue;
                cands.push_back(Cand{ei, qName, rName, n, aPoly, c.reason,
                                      bit->second.lo.reason, bit->second.hi.reason});
            }
        }
    }
    // 2b. Unambiguous remainders (candidate in exactly one equation) first.
    std::unordered_map<std::string, int> rEqCount;
    {
        std::unordered_map<std::string, std::unordered_set<size_t>> rEqs;
        for (const auto& c : cands) rEqs[c.r].insert(c.ei);
        for (const auto& [r, eqs] : rEqs) rEqCount[r] = static_cast<int>(eqs.size());
    }
    std::stable_sort(cands.begin(), cands.end(), [&](const Cand& a, const Cand& b) {
        return (rEqCount[a.r] == 1 ? 0 : 1) < (rEqCount[b.r] == 1 ? 0 : 1);
    });
    // 2c. Greedy accept: a quotient/remainder belongs to one group; an
    //     equation defines one group.
    for (const auto& cd : cands) {
        if (consumed.count(cd.ei)) continue;
        if (moddefVars.count(cd.r) || quotientVars.count(cd.r)) continue;
        if (moddefVars.count(cd.q) || quotientVars.count(cd.q)) continue;
        groups.push_back(ModGroup{cd.r, cd.q, cd.n, cd.aPoly, cd.eqReason, cd.loR, cd.hiR});
        moddefVars.insert(cd.r);
        quotientVars.insert(cd.q);
        consumed.insert(cd.ei);
    }

    // --- 2b. Eliminability: every occurrence of each quotient must be a
    //         sole-variable, exponent-1 monomial whose coefficient is a
    //         multiple of n. Otherwise demote that group. ---
    {
        std::unordered_map<std::string, mpz_class> qn;
        for (const auto& g : groups) qn[g.qVar] = g.n;
        std::unordered_set<std::string> bad;
        for (const auto& c : constraints) {
            auto termsOpt = kernel_.terms(c.poly);
            if (!termsOpt) {
                for (const auto& v : kernel_.variables(c.poly))
                    if (qn.count(v)) bad.insert(v);
                continue;
            }
            for (const auto& t : *termsOpt) {
                bool soleQ = (t.powers.size() == 1 && t.powers[0].second == 1 &&
                              qn.count(std::string(kernel_.varName(t.powers[0].first))));
                for (const auto& [vid, exp] : t.powers) {
                    std::string nm = std::string(kernel_.varName(vid));
                    auto it = qn.find(nm);
                    if (it == qn.end()) continue;
                    if (!soleQ || (t.coefficient % it->second) != 0) bad.insert(nm);
                }
            }
        }
        if (!bad.empty()) {
            std::vector<ModGroup> kept;
            std::unordered_set<size_t> keptConsumed;
            moddefVars.clear(); quotientVars.clear();
            // Rebuild consumed set: we cannot easily map group->eqIdx here, so
            // simply demote bad groups and recompute the consumed eqs below by
            // re-running classification (groups with bad quotient are dropped).
            for (auto& g : groups)
                if (!bad.count(g.qVar)) {
                    kept.push_back(g);
                    moddefVars.insert(g.rVar);
                    quotientVars.insert(g.qVar);
                }
            groups.swap(kept);
            // recompute consumed: an eq is consumed iff it is some kept group's
            // defining equality. Re-detect by reason match (reasons are unique
            // per asserted literal in normalized_).
            std::unordered_set<uint32_t> groupReasons;
            for (const auto& g : groups) groupReasons.insert(g.eqReason.var);
            consumed.clear();
            for (size_t ei : eqIdx)
                if (groupReasons.count(constraints[ei].reason.var)) consumed.insert(ei);
        }
    }

    std::unordered_map<std::string, const ModGroup*> quotientGroup;
    for (const auto& g : groups) quotientGroup[g.qVar] = &g;

    // --- 3. Simple definitions  v := poly(others), v unit-coeff & single-occurrence ---
    std::vector<SimpleDef> simpleDefs;
    std::unordered_set<std::string> simpleVars;
    bool progress = true;
    while (progress) {
        progress = false;
        for (size_t ei : eqIdx) {
            if (consumed.count(ei)) continue;
            const auto& c = constraints[ei];
            auto termsOpt = kernel_.terms(c.poly);
            if (!termsOpt) continue;
            const auto& terms = *termsOpt;
            // count occurrences of each var across monomials
            std::unordered_map<std::string, int> occ;
            for (const auto& t : terms)
                for (const auto& [vid, e] : t.powers)
                    occ[std::string(kernel_.varName(vid))]++;
            for (size_t ti = 0; ti < terms.size(); ++ti) {
                const Term& t = terms[ti];
                if (t.powers.size() != 1 || t.powers[0].second != 1) continue;
                if (t.coefficient != 1 && t.coefficient != -1) continue;
                std::string v = std::string(kernel_.varName(t.powers[0].first));
                if (occ[v] != 1) continue;                       // appears elsewhere
                if (moddefVars.count(v) || quotientVars.count(v) || simpleVars.count(v))
                    continue;
                std::vector<const Term*> rest;
                for (size_t k = 0; k < terms.size(); ++k)
                    if (k != ti) rest.push_back(&terms[k]);
                PolyId restPoly = buildFromTerms(kernel_, rest);
                // v = -rest/coeff ; coeff = ±1
                PolyId defPoly = (t.coefficient == 1) ? kernel_.neg(restPoly) : restPoly;
                simpleDefs.push_back({v, defPoly, c.reason});
                simpleVars.insert(v);
                consumed.insert(ei);
                progress = true;
                break;
            }
        }
    }

    // --- 4. Remaining equalities are check-only; collect Neqs ---
    std::vector<CheckEq> checkEqs;
    for (size_t ei : eqIdx)
        if (!consumed.count(ei))
            checkEqs.push_back({constraints[ei].poly, constraints[ei].reason});
    std::vector<NeqC> neqs;
    for (size_t ni : neqIdx)
        neqs.push_back({constraints[ni].poly, constraints[ni].reason});

    // --- 5. Primary (free) variables ---
    std::unordered_set<std::string> allVars;
    for (const auto& c : constraints)
        for (const auto& v : kernel_.variables(c.poly)) allVars.insert(v);
    std::vector<std::string> primary;
    for (const auto& v : allVars)
        if (!simpleVars.count(v) && !moddefVars.count(v) && !quotientVars.count(v))
            primary.push_back(v);
    std::sort(primary.begin(), primary.end());  // determinism

    static const bool DIAG = std::getenv("XOLVER_NIA_MODULAR_DIAG") != nullptr;
    if (DIAG) {
        std::cerr << "[MODRES] groups=" << groups.size()
                  << " simpleDefs=" << simpleDefs.size()
                  << " checkEqs=" << checkEqs.size()
                  << " neqs=" << neqs.size()
                  << " primary={";
        for (auto& p : primary) std::cerr << p << " ";
        std::cerr << "}\n";
        for (auto& g : groups)
            std::cerr << "  group r=" << g.rVar << " q=" << g.qVar << " n=" << g.n.get_str()
                      << " a=" << kernel_.toString(g.aPoly) << "\n";
        for (auto& sd : simpleDefs)
            std::cerr << "  def " << sd.vVar << " := " << kernel_.toString(sd.defPoly) << "\n";
    }

    // --- 6. Candidate moduli ---
    // base = lcm of all group moduli (so every group's n divides the modulus we
    // enumerate; for all-pow2 groups lcm == max, but mixed n's (e.g. 2,3,256)
    // need the true lcm).
    mpz_class base = 1;
    for (const auto& g : groups) {
        mpz_class gg;
        mpz_gcd(gg.get_mpz_t(), base.get_mpz_t(), g.n.get_mpz_t());
        base = base / gg * g.n;
    }
    mpz_class cap = mpz_class(static_cast<unsigned long>(modulusCap_));
    std::vector<mpz_class> moduli;
    if (base == 1) {
        // No div/mod groups: brute small moduli for a direct residue
        // contradiction (CRT-style coverage incl. composites).
        for (long m : {2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16})
            if (mpz_class(m) <= cap) moduli.push_back(mpz_class(m));
    } else if (base <= cap) {
        for (mpz_class m = base; m <= cap; m *= 2) {
            moduli.push_back(m);
            if (moduli.size() >= 3) break;
        }
    }
    // base > cap (e.g. 2^256) leaves moduli empty: the enumeration loop is
    // skipped and the Hensel-lifting section (step 8) handles the goal modulus.

    // --- evalOpt: value of a poly under residue map (reduced mod m), with
    //     quotient elimination. nullopt = some needed variable not yet known. ---
    std::function<std::optional<mpz_class>(PolyId, const std::unordered_map<std::string,mpz_class>&, const mpz_class&, int)>
    evalOpt = [&](PolyId poly, const std::unordered_map<std::string,mpz_class>& res,
                  const mpz_class& m, int depth) -> std::optional<mpz_class> {
        if (depth > 64) return std::nullopt;
        auto termsOpt = kernel_.terms(poly);
        if (!termsOpt) {
            // opaque: fall back to direct integer eval if all vars known & no quotient
            std::unordered_map<std::string, mpz_class> full;
            for (const auto& v : kernel_.variables(poly)) {
                if (quotientVars.count(v)) return std::nullopt;
                auto it = res.find(v);
                if (it == res.end()) return std::nullopt;
                full[v] = it->second;
            }
            auto val = kernel_.evalInteger(poly, full);
            if (!val) return std::nullopt;
            return modPos(*val, m);
        }
        mpz_class total = 0;
        for (const auto& t : *termsOpt) {
            // does this monomial contain an eliminated quotient?
            const ModGroup* qg = nullptr;
            for (const auto& [vid, e] : t.powers) {
                auto git = quotientGroup.find(std::string(kernel_.varName(vid)));
                if (git != quotientGroup.end()) { qg = git->second; break; }
            }
            mpz_class termVal;
            if (qg) {
                if (t.powers.size() != 1 || t.powers[0].second != 1) return std::nullopt;
                if ((t.coefficient % qg->n) != 0) return std::nullopt;
                auto rit = res.find(qg->rVar);
                if (rit == res.end()) return std::nullopt;
                auto aval = evalOpt(qg->aPoly, res, m, depth + 1);
                if (!aval) return std::nullopt;
                // coeff*q = (coeff/n)*(a - r)
                termVal = (t.coefficient / qg->n) * (*aval - rit->second);
            } else {
                termVal = t.coefficient;
                for (const auto& [vid, e] : t.powers) {
                    auto it = res.find(std::string(kernel_.varName(vid)));
                    if (it == res.end()) return std::nullopt;
                    mpz_class p; mpz_pow_ui(p.get_mpz_t(), it->second.get_mpz_t(),
                                            static_cast<unsigned long>(e));
                    termVal *= p;
                }
            }
            total += termVal;
        }
        return modPos(total, m);
    };

    // Is `poly` an exact-pinned `±r + c` over a moddef remainder with n <= m?
    // Returns (rVar, sign, c) on success.
    auto pinnedNeq = [&](PolyId poly, const mpz_class& m)
        -> std::optional<std::tuple<std::string, int, mpz_class>> {
        auto termsOpt = kernel_.terms(poly);
        if (!termsOpt) return std::nullopt;
        mpz_class c = 0; const Term* vt = nullptr;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) { c += t.coefficient; continue; }
            if (vt) return std::nullopt;
            if (t.powers.size() != 1 || t.powers[0].second != 1) return std::nullopt;
            if (t.coefficient != 1 && t.coefficient != -1) return std::nullopt;
            vt = &t;
        }
        if (!vt) return std::nullopt;
        std::string rv = std::string(kernel_.varName(vt->powers[0].first));
        if (!moddefVars.count(rv)) return std::nullopt;
        for (const auto& g : groups) if (g.rVar == rv && g.n > m) return std::nullopt;
        return std::make_tuple(rv, vt->coefficient > 0 ? 1 : -1, c);
    };

    // --- 7. Try each modulus ---
    for (const mpz_class& m : moduli) {
        // enumeration size = m^|primary|
        mpz_class enumSize = 1;
        bool overBudget = false;
        for (size_t i = 0; i < primary.size(); ++i) {
            enumSize *= m;
            if (enumSize > mpz_class(static_cast<unsigned long>(enumBudget_))) {
                overBudget = true; break;
            }
        }
        if (overBudget) continue;

        bool feasible = false;   // found a residue model for this m
        bool bailed = false;     // could not fully determine -> unsound to refute
        std::vector<mpz_class> odo(primary.size(), 0);
        unsigned long total = (primary.empty()) ? 1 :
            static_cast<unsigned long>(enumSize.get_ui());

        for (unsigned long iter = 0; iter < total && !feasible && !bailed; ++iter) {
            std::unordered_map<std::string, mpz_class> res;
            for (size_t i = 0; i < primary.size(); ++i) res[primary[i]] = odo[i];

            // fixpoint derivation
            bool prog = true;
            while (prog) {
                prog = false;
                for (const auto& g : groups) {
                    if (res.count(g.rVar)) continue;
                    auto aval = evalOpt(g.aPoly, res, m, 0);
                    if (aval) { res[g.rVar] = modPos(*aval, g.n); prog = true; }
                }
                for (const auto& sd : simpleDefs) {
                    if (res.count(sd.vVar)) continue;
                    auto val = evalOpt(sd.defPoly, res, m, 0);
                    if (val) { res[sd.vVar] = *val; prog = true; }
                }
            }
            // all derived determined?
            bool allKnown = true;
            for (const auto& v : simpleVars) if (!res.count(v)) { allKnown = false; break; }
            if (allKnown) for (const auto& v : moddefVars) if (!res.count(v)) { allKnown = false; break; }
            if (!allKnown) { bailed = true; break; }

            // a residue model must satisfy all check-eqs and all pinned Neqs
            bool model = true;
            for (const auto& ce : checkEqs) {
                auto v = evalOpt(ce.poly, res, m, 0);
                if (!v) { bailed = true; break; }
                if (*v != 0) { model = false; break; }
            }
            if (bailed) break;
            if (model) {
                for (const auto& nq : neqs) {
                    auto pin = pinnedNeq(nq.poly, m);
                    if (!pin) continue;             // unusable Neq -> ignore (relaxation)
                    auto [rv, sign, c] = *pin;
                    mpz_class exact = sign * res[rv] + c;   // exact value of the poly
                    if (exact == 0) { model = false; break; }
                }
            }
            if (model) { feasible = true; break; }

            // advance odometer
            for (size_t i = 0; i < primary.size(); ++i) {
                if (++odo[i] < m) break;
                odo[i] = 0;
            }
        }

        if (DIAG) {
            std::cerr << "[MODRES] m=" << m.get_str() << " total=" << total
                      << " feasible=" << feasible << " bailed=" << bailed << "\n";
        }
        if (bailed || feasible) continue;

        // No residue model exists for m => the constraint subset is UNSAT.
        std::unordered_set<uint32_t> seen;
        std::vector<SatLit> clause;
        auto add = [&](SatLit l) { if (seen.insert(l.var).second) clause.push_back(l); };
        for (const auto& g : groups) { add(g.eqReason); add(g.loReason); add(g.hiReason); }
        for (const auto& sd : simpleDefs) add(sd.reason);
        for (const auto& ce : checkEqs) add(ce.reason);
        for (const auto& nq : neqs) if (pinnedNeq(nq.poly, m)) add(nq.reason);
        return {NiaReasoningKind::Conflict, TheoryConflict{std::move(clause)}, std::nullopt};
    }

    // --- 8. Hensel / Newton-doubling lifting (goal modulus past the enum cap) ---
    // For a goal `r = a mod 2^K, r != 1` where a = mult*v_last and v_last is the
    // tail of a Newton chain v_{i+1} = v_i*(2 - mult*v_i): the error
    // E_i = mult*v_i - 1 satisfies E_{i+1} = -E_i^2 (a kernel-verified polynomial
    // identity), so v_2(E_n) = 2^{steps} * v_2(E_1). Prove the small base
    // v_2(E_1) >= k0 = ceil(K / 2^steps) by enumeration at 2^k0; then
    // 2^K | (mult*v_last - 1) => r = 1, contradicting r != 1. Every step is exact
    // => sound UNSAT-only (invariant 7). This lifts modInv32/64/128/Full and the
    // 2^256 EVM cases without enumerating Z/2^K.
    auto log2pow2 = [](const mpz_class& v) -> long {
        if (v <= 0 || mpz_popcount(v.get_mpz_t()) != 1) return -1;
        return static_cast<long>(mpz_sizeinbase(v.get_mpz_t(), 2)) - 1;
    };
    auto findDef = [&](const std::string& v) -> const SimpleDef* {
        for (const auto& sd : simpleDefs) if (sd.vVar == v) return &sd;
        return nullptr;
    };
    const mpz_class enumCap(static_cast<unsigned long>(enumBudget_));

    for (const auto& G : groups) {
        long K = log2pow2(G.n);
        if (K < 1) continue;
        // goal Neq forbidding value 1 on G.rVar
        mpz_class targetC = 0; bool haveGoal = false; SatLit neqReason{SatLit::positive(0)};
        for (const auto& nq : neqs) {
            auto pin = pinnedNeq(nq.poly, G.n);
            if (!pin) continue;
            auto [rv, sign, cc] = *pin;
            if (rv != G.rVar) continue;
            targetC = -cc / sign;  // forbidden value of r
            haveGoal = true; neqReason = nq.reason; break;
        }
        if (!haveGoal || targetC != 1) continue;  // only the modular-inverse form

        // goal dividend = mult * vLast (single monomial, vLast a chain simpleVar)
        auto gtOpt = kernel_.terms(G.aPoly);
        if (!gtOpt || gtOpt->size() != 1) continue;
        const Term& gt = (*gtOpt)[0];
        std::string vLast; int vLastCnt = 0; bool shapeOk = true;
        for (const auto& [vid, exp] : gt.powers) {
            std::string nm = std::string(kernel_.varName(vid));
            if (simpleVars.count(nm) && exp == 1) { vLast = nm; ++vLastCnt; }
        }
        if (vLastCnt != 1) continue;
        PolyId mult = kernel_.mkConst(mpq_class(gt.coefficient));
        for (const auto& [vid, exp] : gt.powers) {
            if (std::string(kernel_.varName(vid)) == vLast) { if (exp != 1) shapeOk = false; continue; }
            mult = kernel_.mul(mult, kernel_.pow(kernel_.mkVar(vid), static_cast<uint32_t>(exp)));
        }
        if (!shapeOk) continue;
        std::unordered_set<std::string> multVars;
        for (const auto& y : kernel_.variables(mult)) multVars.insert(y);

        // walk the Newton chain, verifying E_{i+1} = -E_i^2 at each step
        int steps = 0; std::string v = vLast; std::vector<SatLit> chainReasons;
        while (steps <= 64) {
            const SimpleDef* sd = findDef(v);
            if (!sd) break;  // v is the base (seed), not a Newton step
            std::string vprev; int cnt = 0;
            for (const auto& y : kernel_.variables(sd->defPoly))
                if (!multVars.count(y)) { vprev = y; ++cnt; }
            if (cnt != 1 || vprev == v) break;
            PolyId vprevPoly = kernel_.mkVar(kernel_.getOrCreateVar(vprev));
            PolyId eNext = kernel_.sub(kernel_.mul(mult, sd->defPoly), kernel_.mkOne());
            PolyId ePrev = kernel_.sub(kernel_.mul(mult, vprevPoly), kernel_.mkOne());
            PolyId chk = kernel_.add(eNext, kernel_.pow(ePrev, 2));
            if (!kernel_.isZero(chk)) break;  // not the doubling identity
            ++steps; chainReasons.push_back(sd->reason); v = vprev;
        }
        if (steps < 1 || steps > 62) continue;
        const std::string baseVar = v;

        long k0 = (K + (1L << steps) - 1) / (1L << steps);  // ceil(K / 2^steps)
        if (k0 < 1) k0 = 1;
        if (2L * k0 < 0 || k0 > 40) continue;
        mpz_class mBase = mpz_class(1) << k0;
        if (mBase > mpz_class(static_cast<unsigned long>(modulusCap_))) continue;

        // dependency closure of (mult*baseVar - 1) -> restrict base primaries
        PolyId baseVarPoly = kernel_.mkVar(kernel_.getOrCreateVar(baseVar));
        PolyId baseTarget = kernel_.sub(kernel_.mul(mult, baseVarPoly), kernel_.mkOne());
        std::unordered_set<std::string> closure;
        std::vector<std::string> work = kernel_.variables(baseTarget);
        while (!work.empty()) {
            std::string x = work.back(); work.pop_back();
            if (!closure.insert(x).second) continue;
            if (const SimpleDef* sd = findDef(x))
                for (const auto& y : kernel_.variables(sd->defPoly)) work.push_back(y);
            for (const auto& g : groups) {
                if (g.rVar == x) for (const auto& y : kernel_.variables(g.aPoly)) work.push_back(y);
                if (g.qVar == x) { for (const auto& y : kernel_.variables(g.aPoly)) work.push_back(y); work.push_back(g.rVar); }
            }
        }
        std::vector<std::string> basePrimary;
        for (const auto& p : primary) if (closure.count(p)) basePrimary.push_back(p);

        mpz_class bsize = 1; bool bover = false;
        for (size_t i = 0; i < basePrimary.size(); ++i) {
            bsize *= mBase;
            if (bsize > enumCap) { bover = true; break; }
        }
        if (bover) continue;

        // prove: every valid assignment (mod 2^k0) has mult*baseVar ≡ 1 (mod 2^k0)
        bool baseHolds = true, baseBail = false;
        std::vector<mpz_class> odo(basePrimary.size(), 0);
        unsigned long btotal = basePrimary.empty() ? 1 : static_cast<unsigned long>(bsize.get_ui());
        for (unsigned long it = 0; it < btotal && baseHolds && !baseBail; ++it) {
            std::unordered_map<std::string, mpz_class> res;
            for (size_t i = 0; i < basePrimary.size(); ++i) res[basePrimary[i]] = odo[i];
            bool prog = true;
            while (prog) {
                prog = false;
                for (const auto& g : groups) {
                    if (res.count(g.rVar) || (mBase % g.n) != 0) continue;  // usable groups only
                    auto aval = evalOpt(g.aPoly, res, mBase, 0);
                    if (aval) { res[g.rVar] = modPos(*aval, g.n); prog = true; }
                }
                for (const auto& sd : simpleDefs) {
                    if (res.count(sd.vVar)) continue;
                    auto val = evalOpt(sd.defPoly, res, mBase, 0);
                    if (val) { res[sd.vVar] = *val; prog = true; }
                }
            }
            // validity filter: every EVALUABLE check-eq must hold (a stronger
            // ∀ over a superset of valid assignments is sound)
            bool valid = true;
            for (const auto& ce : checkEqs) {
                auto cv = evalOpt(ce.poly, res, mBase, 0);
                if (cv && *cv != 0) { valid = false; break; }
            }
            if (!valid) { for (size_t i = 0; i < basePrimary.size(); ++i) { if (++odo[i] < mBase) break; odo[i] = 0; } continue; }
            auto bt = evalOpt(baseTarget, res, mBase, 0);
            if (!bt) { baseBail = true; break; }
            if (*bt != 0) { baseHolds = false; break; }
            for (size_t i = 0; i < basePrimary.size(); ++i) { if (++odo[i] < mBase) break; odo[i] = 0; }
        }
        if (baseBail || !baseHolds) continue;
        if (static_cast<long long>(k0) * (1LL << steps) < K) continue;  // 2^steps*k0 >= K

        if (DIAG) {
            std::cerr << "[MODRES-HENSEL] goal r=" << G.rVar << " K=" << K
                      << " vLast=" << vLast << " steps=" << steps
                      << " base=" << baseVar << " k0=" << k0 << " -> UNSAT\n";
        }
        // UNSAT: 2^K | (mult*vLast - 1) => r = 1, contradicting r != 1.
        std::unordered_set<uint32_t> seen;
        std::vector<SatLit> clause;
        auto add = [&](SatLit l) { if (seen.insert(l.var).second) clause.push_back(l); };
        for (const auto& g : groups) { add(g.eqReason); add(g.loReason); add(g.hiReason); }
        for (const auto& sd : simpleDefs) add(sd.reason);
        for (const auto& ce : checkEqs) add(ce.reason);
        add(neqReason);
        return {NiaReasoningKind::Conflict, TheoryConflict{std::move(clause)}, std::nullopt};
    }

    return NO_CHANGE;
}

} // namespace xolver
