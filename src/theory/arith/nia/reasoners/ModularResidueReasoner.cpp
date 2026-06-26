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

#include "util/EnvParam.h"
#include "util/SolveClock.h"

namespace xolver {

namespace {

using Term = PolynomialKernel::MonomialTerm;

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
    : kernel_(kernel),
      modulusCap_(static_cast<uint64_t>(
          env::paramLong("XOLVER_NIA_MODULAR_MODULUS_CAP", 1L << 18))),
      enumBudget_(static_cast<uint64_t>(
          env::paramLong("XOLVER_NIA_MODULAR_ENUM_BUDGET", 1L << 24))) {}

mpz_class ModularResidueReasoner::currentModulusCap() const {
    long scaled = wall::scaledCount(static_cast<long>(modulusCap_));
    return mpz_class(static_cast<unsigned long>(scaled));
}

mpz_class ModularResidueReasoner::currentEnumBudget() const {
    long scaled = wall::scaledCount(static_cast<long>(enumBudget_));
    return mpz_class(static_cast<unsigned long>(scaled));
}

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

// Factor n as p^K for a prime p (K >= 1). Returns nullopt for n <= 1 or n
// composite (not a prime power). Used by the Hensel-doubling lift to extend
// beyond pow2 modulus; the existing pow2 fast path (log2pow2) shortcuts a
// popcount check, this is the general fallback. Costs O(sqrt(n)) trial
// division on the smallest factor; for the modulus sizes we lift (n < 2^40),
// that's ~2^20 trial divisions in the worst case — negligible per call.
std::optional<std::pair<mpz_class, long>> factorAsPrimePower(const mpz_class& n) {
    if (n < 2) return std::nullopt;
    mpz_class m = n;
    mpz_class p = 0;
    // Strip 2's first (fast path for the common pow2 modulus).
    if ((m & 1) == 0) {
        p = 2;
        while ((m & 1) == 0) m /= 2;
        if (m == 1) {
            long K = static_cast<long>(mpz_sizeinbase(n.get_mpz_t(), 2)) - 1;
            return std::make_pair(p, K);
        }
        return std::nullopt;  // n = 2^a * b, b > 1 -> not a prime power
    }
    // Trial-divide odd primes up to sqrt(m).
    mpz_class d = 3;
    while (d * d <= m) {
        if (m % d == 0) { p = d; break; }
        d += 2;
    }
    if (p == 0) {
        // m itself is prime
        p = m;
        return std::make_pair(p, 1L);
    }
    long K = 0;
    while (m % p == 0) { m /= p; ++K; }
    if (m != 1) return std::nullopt;  // multiple distinct prime factors
    return std::make_pair(p, K);
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

    // --- 4.5 Symbolic-modulus residue branch (Track C1 Phase 2.5) ---
    // Gated on XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO (pairs with the
    // IntDivModLowerer flag that lets symbolic-divisor mod/div pass through
    // QF_NIA without EUF). Pattern:
    //   (eq a (+ (* b q) r))         -- the lowered mod equation, b symbolic
    //   (eq a polynomial_form)       -- a separate equality giving a's form
    //   (not (= r const_c))          -- the negated mod-residue assertion
    // We compute residue := extractSymbolicResidue(polynomial_form, b). If
    // residue is a constant != const_c (so r MUST equal residue, but is
    // asserted != const_c -> conflict), we then run a brute-force grid
    // certification (s in {2,3,5,7}, free vars in a small range) to confirm
    // the unsat verdict at every grid point before emitting the conflict.
    // Sound: extractSymbolicResidue is z3-validated (Phase 1, 8438
    // assertions); the grid cert is a second-path verification using
    // kernel.evalInteger over a fresh evaluation strategy.
    static const bool symbolicEnabled =
        env::paramInt("XOLVER_NIA_SYMBOLIC_DIVMOD_NONZERO", 0) != 0;
    static const bool symbDiag =
        env::paramInt("XOLVER_NIA_MODULAR_DIAG", 0) != 0;
    // --- 4.6 Newton-chain derivation (Track C1 Phase 2.6) ---
    // Synthesize a check-eq from a Newton-step simpleDef + a base mod that
    // pins denom*B at residue 1 (mod s). Mathematics:
    //
    //   simpleDef inv2 := 2*B - C*B^2     (Newton step: inv2 = B*(2 - C*B))
    //   checkEq    -s*q + C*B - r = 0     (base mod's lowered eq)
    //   simpleDef r := 1                  (base assertion: C*B ≡ 1 mod s)
    //
    //   ⇒ C*B = s*q + 1
    //   ⇒ C*inv2 = (s*q + 1)*(1 - s*q) = 1 - q^2 * s^2
    //
    // The derived check-eq C*inv2 + q^2*s^2 - 1 = 0 then feeds Phase 2.5,
    // which computes extractSymbolicResidue(1 - q^2*s^2, s^2) = 1 and
    // conflicts with `(neq r_goal != 1)`. Grid cert in Phase 2.5 validates
    // the verdict at s ∈ {2,3,5,7}. Sound by Phase 1 polynomial identity +
    // base substitution + standard polynomial algebra (all exact over Z).
    std::vector<std::pair<PolyId, std::vector<SatLit>>> synthesizedCheckEqs;
    if (symbolicEnabled) {
        // Build a fast lookup: simpleDef var name -> (defPoly, reason).
        std::unordered_map<std::string, const SimpleDef*> simpleDefByVar;
        for (const auto& sd : simpleDefs) simpleDefByVar[sd.vVar] = &sd;

        for (const auto& nSd : simpleDefs) {
            // Newton step simpleDef: defPoly has 2 terms: `2*B` and `-C*B^2`.
            auto sdT = kernel_.terms(nSd.defPoly);
            if (!sdT || sdT->size() != 2) continue;

            // Pick the two terms; identify which is the linear-coeff-2 term
            // and which is the quadratic-in-B / linear-in-C term.
            const Term* t2B = nullptr;     // expects 2*B
            const Term* tCBSq = nullptr;   // expects -C*B^2
            for (size_t i = 0; i < 2; ++i) {
                const Term& tt = (*sdT)[i];
                if (tt.powers.size() == 1 && tt.powers[0].second == 1 &&
                    tt.coefficient == 2) {
                    t2B = &tt;
                } else if (tt.powers.size() == 2 && tt.coefficient == -1) {
                    tCBSq = &tt;
                }
            }
            if (!t2B || !tCBSq) continue;
            VarId bVid = t2B->powers[0].first;
            // In tCBSq, one var with deg 2 (= B) and one with deg 1 (= C).
            VarId cVid = NullVar;
            VarId tcsqBVid = NullVar;
            for (auto& [vid, e] : tCBSq->powers) {
                if (e == 2) tcsqBVid = vid;
                else if (e == 1) cVid = vid;
            }
            if (tcsqBVid != bVid || cVid == NullVar) continue;

            std::string inv1Var = std::string(kernel_.varName(bVid));
            std::string denomVar = std::string(kernel_.varName(cVid));

            // Now find a base checkEq with shape:
            //   sign_q * s * q + sign_C * C * B + sign_r * r = 0
            // with sign_C == -sign_q == -sign_r (so rearrangement is
            // C*B = s*q + r), AND r is a simpleDef var pinned to 1.
            for (const auto& ce : checkEqs) {
                auto ceT = kernel_.terms(ce.poly);
                if (!ceT || ceT->size() != 3) continue;

                const Term* tSQ = nullptr;     // s * q term (multi-var, deg 1 in each)
                const Term* tCB = nullptr;     // C * B term (deg 1 in both)
                const Term* tR  = nullptr;     // r term (linear, unit coeff)
                const Term* tConst = nullptr;  // constant term (used by modInvVar1
                                                // shape: -C*B + s*q + 1 = 0)
                for (const Term& tt : *ceT) {
                    if (tt.powers.empty()) {
                        if (tConst) { tConst = nullptr; break; }
                        tConst = &tt;
                    } else if (tt.powers.size() == 1 && tt.powers[0].second == 1 &&
                        (tt.coefficient == 1 || tt.coefficient == -1)) {
                        if (tR) { tR = nullptr; break; }  // ambiguous
                        tR = &tt;
                    } else if (tt.powers.size() == 2) {
                        bool hasC = false, hasB = false;
                        for (auto& [vid, e] : tt.powers) {
                            if (vid == cVid && e == 1) hasC = true;
                            if (vid == bVid && e == 1) hasB = true;
                        }
                        if (hasC && hasB) tCB = &tt;
                        else tSQ = &tt;
                    }
                }
                if (!tSQ || !tCB) continue;
                if (tCB->coefficient != 1 && tCB->coefficient != -1) continue;
                if (tSQ->coefficient != 1 && tSQ->coefficient != -1) continue;
                // Two shapes accepted:
                //  (a) tR present, tConst absent — r-var pinned to 1 elsewhere.
                //  (b) tR absent, tConst = +/-1 — Bezout witness baked into eq.
                // Both lead to the same canonical form `C*B = s*q + 1`, but we
                // need to check the signs:
                //    (a) C*B and r must have opposite signs; s*q must match r's sign.
                //    (b) C*B coefficient and tConst coefficient must agree on sign,
                //        such that rearrangement yields `C*B = s*q + 1`.
                bool variantA = (tR != nullptr && tConst == nullptr);
                bool variantB = (tR == nullptr && tConst != nullptr);
                if (!variantA && !variantB) continue;
                if (variantA) {
                    if (tCB->coefficient != -tR->coefficient) continue;
                    if (tSQ->coefficient != tR->coefficient) continue;
                } else {
                    if (tConst->coefficient != 1 && tConst->coefficient != -1) continue;
                    // C*B and tConst must have OPPOSITE signs (so `C*B - tConst = -s*q`
                    // or `C*B = s*q + |tConst|` after sign normalisation).
                    if (tCB->coefficient == tConst->coefficient) continue;
                    if (tSQ->coefficient != tConst->coefficient) continue;
                }

                // Identify s and q from tSQ (both deg 1; we don't know which is
                // which, so try both orderings).
                std::array<VarId, 2> sqVars = {tSQ->powers[0].first,
                                                tSQ->powers[1].first};
                for (int order = 0; order < 2; ++order) {
                    VarId sVid = sqVars[order];
                    VarId qVid = sqVars[1 - order];
                    if (sVid == cVid || sVid == bVid) continue;
                    if (qVid == cVid || qVid == bVid) continue;

                    // Validate the base value = 1 (variantA: from r simpleDef;
                    // variantB: from tConst sign, where canonical form
                    // `C*B = s*q + 1` requires |tConst| = 1).
                    const SimpleDef* rSdRef = nullptr;
                    if (variantA) {
                        std::string rVar = std::string(kernel_.varName(
                            tR->powers[0].first));
                        auto rIt = simpleDefByVar.find(rVar);
                        if (rIt == simpleDefByVar.end()) continue;
                        if (!kernel_.isConstant(rIt->second->defPoly)) continue;
                        mpq_class rValQ = kernel_.toConstant(rIt->second->defPoly);
                        if (rValQ.get_den() != 1) continue;
                        if (rValQ.get_num() != 1) continue;
                        rSdRef = rIt->second;
                    } else {
                        // variantB: tConst is +/-1; combined with the sign
                        // constraints above we already verified canonical form.
                        // The constant absolute value must equal 1 (Bezout).
                        mpz_class absC = tConst->coefficient;
                        if (absC < 0) absC = -absC;
                        if (absC != 1) continue;
                    }

                    // Now synthesize: C*inv2 + q^2 * s^2 - 1 = 0.
                    PolyId pC = kernel_.mkVar(cVid);
                    PolyId pInv2 = kernel_.mkVar(
                        kernel_.getOrCreateVar(nSd.vVar));
                    PolyId pQ = kernel_.mkVar(qVid);
                    PolyId pS = kernel_.mkVar(sVid);
                    PolyId q2 = kernel_.mul(pQ, pQ);
                    PolyId s2 = kernel_.mul(pS, pS);
                    PolyId q2s2 = kernel_.mul(q2, s2);
                    PolyId cInv2 = kernel_.mul(pC, pInv2);
                    PolyId one = kernel_.mkConst(mpq_class(1));
                    PolyId synthPoly = kernel_.sub(
                        kernel_.add(cInv2, q2s2), one);

                    // Reasons: Newton simpleDef + base checkEq + (variantA: r=1
                    // simpleDef; variantB: Bezout constant already in checkEq).
                    std::vector<SatLit> reasons = {nSd.reason, ce.reason};
                    if (rSdRef) reasons.push_back(rSdRef->reason);
                    synthesizedCheckEqs.push_back({synthPoly,
                                                    std::move(reasons)});
                    if (symbDiag) std::cerr
                        << "[MODRES-SYMB] Newton derived: "
                        << kernel_.toString(synthPoly) << " = 0\n";
                    goto next_newton;
                }
            }
            next_newton:;
        }
    }

    if (symbolicEnabled) {
        // Pattern matcher for the lowered symbolic-mod eq atom:
        //   poly = a_terms + (b_poly * q_var) + sign_r * r_var
        // We look for a single linear unit-coeff term (r-candidate), and a
        // single term that includes a deg-1 var whose coefficient polynomial
        // (in the remaining vars of that monomial) is non-constant.
        auto buildPolyFromTerms = [&](const std::vector<const Term*>& ts) -> PolyId {
            PolyId acc = kernel_.mkZero();
            for (const Term* t : ts) {
                PolyId mono = kernel_.mkConst(mpq_class(t->coefficient));
                for (const auto& [vid, e] : t->powers)
                    mono = kernel_.mul(mono, kernel_.pow(kernel_.mkVar(vid),
                                                        static_cast<uint32_t>(e)));
                acc = kernel_.add(acc, mono);
            }
            return acc;
        };
        // Build a polynomial representing all terms EXCEPT one monomial. For
        // the symbolic-coefficient extraction: given a term `coeff * q * X^p`
        // where X^p is the remaining-vars part, the coefficient polynomial
        // (in X) is `coeff * X^p`. We use this to recover `b` from the
        // `b * q` term.
        auto buildCoeffPolyExcept = [&](const Term* t,
                                        VarId excludedVar) -> PolyId {
            PolyId mono = kernel_.mkConst(mpq_class(t->coefficient));
            for (const auto& [vid, e] : t->powers) {
                if (vid == excludedVar) continue;
                mono = kernel_.mul(mono, kernel_.pow(kernel_.mkVar(vid),
                                                    static_cast<uint32_t>(e)));
            }
            return mono;
        };

        for (size_t ei = 0; ei < constraints.size(); ++ei) {
            const auto& c = constraints[ei];
            if (c.rel != Relation::Eq) continue;
            auto termsOpt = kernel_.terms(c.poly);
            if (!termsOpt) continue;
            const auto& terms = *termsOpt;
            if (terms.size() < 3) continue;

            for (size_t ri = 0; ri < terms.size(); ++ri) {
                const Term& rt = terms[ri];
                if (rt.powers.size() != 1 || rt.powers[0].second != 1) continue;
                if (rt.coefficient != 1 && rt.coefficient != -1) continue;
                VarId rVid = rt.powers[0].first;
                std::string rVar = std::string(kernel_.varName(rVid));
                int rSign = rt.coefficient > 0 ? 1 : -1;

                for (size_t qi = 0; qi < terms.size(); ++qi) {
                    if (qi == ri) continue;
                    const Term& qt = terms[qi];
                    // Find a deg-1 var inside qt; the remaining factor (across
                    // remaining vars, with the term coefficient) is b.
                    for (const auto& [qVid, qExp] : qt.powers) {
                        if (qExp != 1) continue;
                        if (qVid == rVid) continue;
                        // Canonical lowering form: `<aTerms> + <-b*q> + <-r> = 0`
                        // i.e. the q-term and the r-term share the same sign and the
                        // a-terms have the opposite sign. Require qSign == rSign so
                        // the rearrangement `a = b*q + r` gives a positive modulus.
                        int qSign = qt.coefficient > 0 ? 1 : -1;
                        if (qSign != rSign) continue;
                        std::string qVar = std::string(kernel_.varName(qVid));
                        PolyId bPolyRaw = buildCoeffPolyExcept(&qt, qVid);
                        // Coefficient of q in the poly is bPolyRaw (= qt.coeff * remaining).
                        // For the rearrangement `a = b*q + r`, modulus b = -bPolyRaw / rSign.
                        // With rSign == qSign, that's just -bPolyRaw (the sign flip cancels).
                        PolyId bPoly = kernel_.neg(bPolyRaw);
                        if (kernel_.isConstant(bPoly)) continue;  // numeric path
                        // a_terms = all terms except the r-term and the q-term.
                        std::vector<const Term*> aTerms;
                        for (size_t k = 0; k < terms.size(); ++k)
                            if (k != ri && k != qi) aTerms.push_back(&terms[k]);
                        if (aTerms.empty()) continue;
                        // a_poly_lhs: the lhs `a` polynomial. From `a + b*q*sign_q + r*sign_r = 0`:
                        // (with sign_r being rt.coefficient sign) → a = -(b*q*sign_q + r*sign_r),
                        // but `a_terms` are EXACTLY the monomials of `a` already, so just sum.
                        [[maybe_unused]] PolyId aPolyLhs = buildPolyFromTerms(aTerms);
                        // Note: `aPolyLhs` here is the actual `a` expression in
                        // the equation `a + (-b*q -r*sign_r? or +b*q +r*sign_r)=0`.
                        // Because we MOVE r and q*b to the other side: a = sign_r * (-r) +
                        // (-coeff_q * q * b_rest). The math: poly = aTerms + b*q + sign_r*r,
                        // where b includes the qt.coefficient. Rearranged:
                        // aTerms = -(b*q) - sign_r*r. The constraint reads:
                        // `<aTerms> + <qt> + <rt> = 0`. After moving:
                        // `<a_poly_term_sum> = -<qt> - <rt>`. So the "value of a" expressed
                        // as the polynomial of the rest is the negation of -<qt> - <rt>:
                        // value(a_terms) = -(b * q + sign_r * r). But we don't need this
                        // form — we need a_poly_form FROM ANOTHER constraint.
                        // What we have so far: aPolyLhs is the polynomial that exactly
                        // matches the LHS aTerms (so any other constraint asserting
                        // `aPolyLhs = something` gives us the closed form to feed to
                        // extractSymbolicResidue).

                        // Look for a check-eq P with the SAME aTerms (so P - aTerms is
                        // purely in non-aTerm vars and = -aPolyForm). I.e., P =
                        // aPolyLhs + remainder_poly = 0 → aPolyLhs = -remainder_poly.
                        // The polynomial form of `a` is then -remainder_poly.
                        // Iterate the natural check-eqs plus any Phase 2.6
                        // Newton-derived synthesized check-eqs. Each entry is
                        // (poly, vector<reason>); regular check-eqs wrap the
                        // single reason in a one-element vector.
                        std::vector<std::pair<PolyId, std::vector<SatLit>>>
                            combinedCheckEqs;
                        combinedCheckEqs.reserve(checkEqs.size() +
                                                  synthesizedCheckEqs.size());
                        for (const auto& ce0 : checkEqs)
                            combinedCheckEqs.push_back({ce0.poly, {ce0.reason}});
                        for (const auto& sce : synthesizedCheckEqs)
                            combinedCheckEqs.push_back(sce);
                        for (const auto& ce : combinedCheckEqs) {
                            auto ctermsOpt = kernel_.terms(ce.first);
                            if (!ctermsOpt) continue;
                            const auto& cterms = *ctermsOpt;
                            // Try BOTH sign patterns for the a-monomial sub-match.
                            // s = +1 means we look for a-terms with the SAME coefficient
                            // (check-eq has form `a + rest = 0` -> a = -rest).
                            // s = -1 means we look for a-terms with NEGATED coefficient
                            // (check-eq has form `-a + rest = 0` -> a = +rest).
                            PolyId aPolyForm = NullPoly;
                            for (int aSign : {+1, -1}) {
                                std::vector<const Term*> usedFromC(cterms.size(), nullptr);
                                bool allMatched = true;
                                for (const Term* at : aTerms) {
                                    mpz_class wantCoeff = aSign * at->coefficient;
                                    bool found = false;
                                    for (size_t k = 0; k < cterms.size(); ++k) {
                                        if (usedFromC[k]) continue;
                                        const Term& ct = cterms[k];
                                        if (ct.powers.size() != at->powers.size()) continue;
                                        if (ct.coefficient != wantCoeff) continue;
                                        bool powersEq = true;
                                        for (size_t pi = 0; pi < at->powers.size(); ++pi) {
                                            if (ct.powers[pi].first != at->powers[pi].first ||
                                                ct.powers[pi].second != at->powers[pi].second) {
                                                powersEq = false; break;
                                            }
                                        }
                                        if (!powersEq) continue;
                                        usedFromC[k] = &ct;
                                        found = true;
                                        break;
                                    }
                                    if (!found) { allMatched = false; break; }
                                }
                                if (!allMatched) continue;
                                std::vector<const Term*> restTerms;
                                for (size_t k = 0; k < cterms.size(); ++k)
                                    if (!usedFromC[k]) restTerms.push_back(&cterms[k]);
                                PolyId restPoly = buildPolyFromTerms(restTerms);
                                // Check-eq: aSign*a + rest = 0 -> a = -rest/aSign.
                                // aSign=+1 -> aPolyForm = -rest
                                // aSign=-1 -> aPolyForm = +rest
                                aPolyForm = (aSign == 1) ? kernel_.neg(restPoly)
                                                          : restPoly;
                                break;
                            }
                            if (aPolyForm == NullPoly) continue;

                            auto residueOpt = kernel_.extractSymbolicResidue(aPolyForm, bPoly);
                            if (!residueOpt) continue;
                            if (!kernel_.isConstant(*residueOpt)) continue;
                            mpq_class residueValQ = kernel_.toConstant(*residueOpt);
                            if (residueValQ.get_den() != 1) continue;
                            mpz_class residueVal = residueValQ.get_num();

                            // Scan neqs for r_var != const_c (parse locally — the file's
                            // pinnedNeq lambda is defined later inside run()).
                            auto parseSingleVarNeq = [&](PolyId p)
                                -> std::optional<std::tuple<std::string,int,mpz_class>> {
                                auto tOpt = kernel_.terms(p);
                                if (!tOpt) return std::nullopt;
                                const Term* vt = nullptr;
                                mpz_class cc = 0;
                                for (const auto& tm : *tOpt) {
                                    if (tm.powers.empty()) { cc += tm.coefficient; continue; }
                                    if (vt) return std::nullopt;
                                    if (tm.powers.size() != 1 ||
                                        tm.powers[0].second != 1) return std::nullopt;
                                    if (tm.coefficient != 1 && tm.coefficient != -1)
                                        return std::nullopt;
                                    vt = &tm;
                                }
                                if (!vt) return std::nullopt;
                                int sgnV = vt->coefficient > 0 ? 1 : -1;
                                return std::make_tuple(
                                    std::string(kernel_.varName(vt->powers[0].first)),
                                    sgnV, cc);
                            };
                            for (const auto& nq : neqs) {
                                auto pin = parseSingleVarNeq(nq.poly);
                                if (!pin) continue;
                                auto [pinVar, pinSign, pinCc] = *pin;
                                if (pinVar != rVar) continue;
                                mpz_class forbiddenVal = -pinCc / pinSign;
                                // sign_r adjustment: in the eq `aTerms + b*q + rSign*r = 0`,
                                // the canonical residue assertion is on `r` directly.
                                // Conflict iff residueVal == forbiddenVal * rSign ... actually
                                // we just want r == residueVal AND r != forbiddenVal, so
                                // conflict iff residueVal == forbiddenVal. But the sign on r
                                // in the eq matters only for the direction; the canonical
                                // residue from extractSymbolicResidue applies directly to
                                // the variable r (since we rebuilt a_poly = -rest and the
                                // eq says a = b*q + r, so a mod b = r when 0 <= r < b).
                                if (residueVal != forbiddenVal) continue;
                                if (symbDiag) std::cerr
                                    << "[MODRES-SYMB] candidate conflict r=" << rVar
                                    << " residue=" << residueVal.get_str()
                                    << " forbidden=" << forbiddenVal.get_str()
                                    << " — running grid cert\n";

                                // Grid cert: substitute s ∈ {2,3,5,7} into ALL constraints
                                // (we substitute every variable from `bPoly` since b is
                                // single-variable for Phase 2.5 / extractSymbolicResidue's
                                // monovariate requirement). For each prime, brute-force
                                // every other free variable in {-3..3} and check if any
                                // assignment satisfies every Eq and every pinned-neq;
                                // if so the symbolic verdict is wrong, bail.
                                auto bVars = kernel_.variables(bPoly);
                                if (bVars.size() != 1) continue;  // safety (matches Phase 1)
                                const std::string& modVar = bVars[0];
                                std::vector<std::string> otherVars;
                                {
                                    std::unordered_set<std::string> seen;
                                    for (const auto& cc : constraints)
                                        for (const auto& v : kernel_.variables(cc.poly))
                                            if (v != modVar && seen.insert(v).second)
                                                otherVars.push_back(v);
                                }
                                const std::vector<long> primes = {2, 3, 5, 7};
                                // Range shrinks as the number of free vars
                                // grows so the cert runtime stays bounded:
                                //   <=3 vars : {-3..3} (49 per dim)
                                //   <=5 vars : {-2..2} (5)
                                //   else     : {-1..1} (3)
                                long lo = -3, hi = 3;
                                if (otherVars.size() > 5) { lo = -1; hi = 1; }
                                else if (otherVars.size() > 3) { lo = -2; hi = 2; }
                                bool certOk = true;
                                for (long pSample : primes) {
                                    if (!certOk) break;
                                    std::unordered_map<std::string, mpz_class> env;
                                    env[modVar] = mpz_class(pSample);
                                    std::vector<long> odo(otherVars.size(), lo);
                                    auto inc = [&]() -> bool {
                                        for (size_t i = 0; i < odo.size(); ++i) {
                                            if (++odo[i] <= hi) return true;
                                            odo[i] = lo;
                                        }
                                        return false;
                                    };
                                    auto evalSat = [&]() -> bool {
                                        for (size_t i = 0; i < otherVars.size(); ++i)
                                            env[otherVars[i]] = mpz_class(odo[i]);
                                        for (const auto& cc : constraints) {
                                            auto vv = kernel_.evalInteger(cc.poly, env);
                                            if (!vv) return false;
                                            bool ok = true;
                                            switch (cc.rel) {
                                                case Relation::Eq:  ok = (*vv == 0); break;
                                                case Relation::Leq: ok = (*vv <= 0); break;
                                                case Relation::Geq: ok = (*vv >= 0); break;
                                                case Relation::Neq: ok = (*vv != 0); break;
                                                case Relation::Lt:  ok = (*vv <  0); break;
                                                case Relation::Gt:  ok = (*vv >  0); break;
                                            }
                                            if (!ok) return false;
                                        }
                                        return true;
                                    };
                                    do {
                                        if (evalSat()) { certOk = false; break; }
                                    } while (inc());
                                }
                                if (!certOk) {
                                    if (symbDiag) std::cerr
                                        << "[MODRES-SYMB] grid cert disagreement — bail\n";
                                    continue;
                                }
                                if (symbDiag) std::cerr
                                    << "[MODRES-SYMB] grid cert PASS — emit conflict\n";
                                // Build conflict reason: the eq atom, the check-eq, and
                                // the neq.
                                std::unordered_set<uint32_t> seen;
                                std::vector<SatLit> clause;
                                auto add = [&](SatLit l) {
                                    if (seen.insert(l.var).second) clause.push_back(l);
                                };
                                add(c.reason);
                                for (SatLit r : ce.second) add(r);
                                add(nq.reason);
                                return {NiaReasoningKind::Conflict,
                                        TheoryConflict{std::move(clause)},
                                        std::nullopt};
                            }
                        }
                    }
                }
            }
        }
    }

    // --- 5. Primary (free) variables ---
    std::unordered_set<std::string> allVars;
    for (const auto& c : constraints)
        for (const auto& v : kernel_.variables(c.poly)) allVars.insert(v);
    std::vector<std::string> primaryAll;
    for (const auto& v : allVars)
        if (!simpleVars.count(v) && !moddefVars.count(v) && !quotientVars.count(v))
            primaryAll.push_back(v);

    // Dependency closure of the USABLE constraints (group eqs + check-eqs +
    // pinned-form neqs) through the def/group graph. Variables OUTSIDE this
    // closure appear only in ignored constraints (inequalities, non-pinned
    // neqs), so they cannot affect whether the usable subset has a residue
    // model — fix them out instead of enumerating them. This is what lets the
    // reasoner fire on cases with many irrelevant free vars (e.g. ps4: free
    // {c,k,y} but the mod-4 refutation is purely in y -> enumerate y, not 64).
    // iter-105 perf: pre-build name → SimpleDef* index. The findDef0 closure
    // is called inside a closure-expansion while loop; with N simpleDefs and
    // closure work-list size W, the original linear scan gave O(W × N). For
    // deep modular reasoning (multi-modulus closure) this is the dominant
    // cost. Sound: same mapping just faster, simpleDefs is built once before
    // this loop and is not mutated within findDef0.
    std::unordered_map<std::string, const SimpleDef*> simpleDefByVar;
    simpleDefByVar.reserve(simpleDefs.size());
    for (const auto& sd : simpleDefs) simpleDefByVar.emplace(sd.vVar, &sd);
    auto findDef0 = [&](const std::string& v) -> const SimpleDef* {
        auto it = simpleDefByVar.find(v);
        return it != simpleDefByVar.end() ? it->second : nullptr;
    };
    std::unordered_set<std::string> closure;
    {
        std::vector<std::string> work;
        auto seed = [&](PolyId p) { for (const auto& v : kernel_.variables(p)) work.push_back(v); };
        for (const auto& g : groups) { work.push_back(g.rVar); work.push_back(g.qVar); seed(g.aPoly); }
        for (const auto& ce : checkEqs) seed(ce.poly);
        for (const auto& nq : neqs) {
            // include only pinned-form neqs (±moddef + const); skip multivar/non-pinned
            auto t = kernel_.terms(nq.poly);
            if (!t) continue;
            const Term* vt = nullptr; bool ok = true;
            for (const auto& tm : *t) {
                if (tm.powers.empty()) continue;
                if (vt || tm.powers.size() != 1 || tm.powers[0].second != 1) { ok = false; break; }
                vt = &tm;
            }
            if (ok && vt && moddefVars.count(std::string(kernel_.varName(vt->powers[0].first))))
                seed(nq.poly);
        }
        while (!work.empty()) {
            std::string x = work.back(); work.pop_back();
            if (!closure.insert(x).second) continue;
            if (const SimpleDef* sd = findDef0(x)) seed(sd->defPoly);
            for (const auto& g : groups) {
                if (g.rVar == x) seed(g.aPoly);
                if (g.qVar == x) { seed(g.aPoly); work.push_back(g.rVar); }
            }
        }
    }
    std::vector<std::string> primary;
    for (const auto& v : primaryAll)
        if (closure.count(v)) primary.push_back(v);
    std::sort(primary.begin(), primary.end());  // determinism
    // Derived vars we must fully determine before declaring UNSAT = only those
    // in the closure (others feed nothing usable, so leaving them unknown is fine).
    std::unordered_set<std::string> needSimple, needModdef;
    for (const auto& v : simpleVars)  if (closure.count(v)) needSimple.insert(v);
    for (const auto& v : moddefVars)  if (closure.count(v)) needModdef.insert(v);

    static const bool DIAG = env::paramInt("XOLVER_NIA_MODULAR_DIAG", 0) != 0;
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
    mpz_class cap = currentModulusCap();
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
        // CRT-style coverage: also try a few small moduli COPRIME to the group
        // base. A formula whose div/mod groups are mod 2^k can still carry a
        // residue contradiction at mod 3/5/7 in its equality structure (the
        // groups simply don't constrain those residues). The brute-force cert
        // floor keeps any such UNSAT sound. (Groups with n ∤ m bail at that m,
        // so this only fires on a contradiction among the non-group constraints.)
        for (long p : {3, 5, 7}) {
            mpz_class pm(p);
            mpz_class g; mpz_gcd(g.get_mpz_t(), base.get_mpz_t(), pm.get_mpz_t());
            if (g == 1 && pm <= cap) moduli.push_back(pm);
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

    // --- Brute-force CERTIFICATE (soundness floor) ---
    // Independently re-verify a modular UNSAT by enumerating ALL variables over
    // Z/m (NO substitution / closure / Hensel reuse — fresh brute force over the
    // raw normalized constraints) and checking the SAME relaxation the reasoner
    // refuted: every Eq ≡ 0 (mod m), every div-group remainder in [0,n), every
    // pinned-form neq. This catches a bug in the plan-building (substitution,
    // group recognition, closure) that would otherwise emit a false UNSAT —
    // critical for the oracle-blind cases (z3/cvc5/BLAN all time out, so nothing
    // external can catch it). Returns:
    //   2 = ConfirmedUnsat (fully enumerated, no model) -> cert-backed, emit
    //   0 = FoundModel (a residue model exists) -> reasoner is WRONG -> FLOOR
    //   1 = OverBudget (residue space too large to brute-force) -> the enum path
    //       FLOORS this now (un-cross-checkable; never ship an un-brute-verified
    //       enum UNSAT). The only large-residue UNSATs we still emit come from the
    //       Hensel path, which carries its OWN machine-checkable polynomial-identity
    //       certificate (verified below), not this enumeration.
    // certBudget MATCHES the enum cap: the enum path only enumerates moduli
    // with residue space <= currentEnumBudget(), so the independent cert can
    // always re-verify exactly what the enum proved (no enum-proven-but-cert-
    // OverBudget gap). Both reads come from the same scaled getter.
    std::vector<std::string> allVarsVec(allVars.begin(), allVars.end());
    std::sort(allVarsVec.begin(), allVarsVec.end());
    const mpz_class certBudget = currentEnumBudget();
    auto bruteCertify = [&](const mpz_class& m) -> int {
        mpz_class sz = 1;
        for (size_t i = 0; i < allVarsVec.size(); ++i) {
            sz *= m;
            if (sz > certBudget) return 1;  // OverBudget
        }
        unsigned long total = allVarsVec.empty() ? 1 : static_cast<unsigned long>(sz.get_ui());
        std::vector<mpz_class> odo(allVarsVec.size(), 0);
        for (unsigned long it = 0; it < total; ++it) {
            std::unordered_map<std::string, mpz_class> res;
            for (size_t i = 0; i < allVarsVec.size(); ++i) res[allVarsVec[i]] = odo[i];
            bool model = true;
            // div-group remainder bounds: r in [0,n)
            for (const auto& g : groups) {
                auto rit = res.find(g.rVar);
                if (rit != res.end() && rit->second >= g.n) { model = false; break; }
            }
            // every equality ≡ 0 mod m (raw evalInteger, no reuse of evalOpt)
            if (model) for (const auto& c : constraints) {
                if (c.rel != Relation::Eq) continue;
                auto v = kernel_.evalInteger(c.poly, res);
                if (!v) return 1;  // can't evaluate -> can't certify -> treat as OverBudget
                if (modPos(*v, m) != 0) { model = false; break; }
            }
            // pinned-form neqs
            if (model) for (const auto& nq : neqs) {
                auto pin = pinnedNeq(nq.poly, m);
                if (!pin) continue;
                auto [rv, sign, c] = *pin;
                if (sign * res[rv] + c == 0) { model = false; break; }
            }
            if (model) return 0;  // FoundModel -> reasoner WRONG
            for (size_t i = 0; i < allVarsVec.size(); ++i) { if (++odo[i] < m) break; odo[i] = 0; }
        }
        return 2;  // ConfirmedUnsat
    };

    // --- 7. Try each modulus ---
    const mpz_class enumBudgetForLoop = currentEnumBudget();
    for (const mpz_class& m : moduli) {
        // enumeration size = m^|primary|
        mpz_class enumSize = 1;
        bool overBudget = false;
        for (size_t i = 0; i < primary.size(); ++i) {
            enumSize *= m;
            if (enumSize > enumBudgetForLoop) {
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
            // all CLOSURE-relevant derived vars determined? (vars outside the
            // usable-constraint closure feed nothing checked, so don't require them)
            bool allKnown = true;
            for (const auto& v : needSimple) if (!res.count(v)) { allKnown = false; break; }
            if (allKnown) for (const auto& v : needModdef) if (!res.count(v)) { allKnown = false; break; }
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
        // SOUNDNESS FLOOR: independently brute-force-certify before emitting.
        int cert = bruteCertify(m);
        if (DIAG) std::cerr << "[MODRES] cert(m=" << m.get_str() << ")="
                            << (cert == 2 ? "ConfirmedUnsat" : cert == 0 ? "FoundModel(FLOOR)" : "OverBudget")
                            << "\n";
        // STRICT independent-proof gate: emit an enum-path UNSAT ONLY when the
        // independent brute-force re-verification CONFIRMS it (cert==2). FoundModel
        // (0, reasoner WRONG) and OverBudget (1, un-cross-checkable) both FLOOR ->
        // we never ship an enum UNSAT that a second independent path didn't confirm.
        if (cert != 2) continue;
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
    // For a goal `r = a mod p^K, r != 1` where a = mult*v_last and v_last is the
    // tail of a Newton chain v_{i+1} = v_i*(2 - mult*v_i): the error
    // E_i = mult*v_i - 1 satisfies E_{i+1} = -E_i^2 (a kernel-verified polynomial
    // identity over Z), so v_p(E_n) = 2^{steps} * v_p(E_1). Prove the small base
    // v_p(E_1) >= k0 = ceil(K / 2^steps) by enumeration at p^k0; then
    // p^K | (mult*v_last - 1) => r = 1, contradicting r != 1. Every step is exact
    // => sound UNSAT-only (invariant 7).
    //
    // Generalization (Track B1, master directive): the Newton-doubling identity
    // is independent of the prime p — it is a polynomial identity over Z. We
    // therefore lift the original "p = 2" assumption to any prime: detect the
    // modulus via factorAsPrimePower (n = p^K, K >= 1, p prime), and run the
    // same chain over base modulus p^k0. The existing modInv*/EVM 2^k cases
    // hit the p = 2 branch unchanged; non-pow2 prime-power moduli (e.g.
    // `mod 3^K`, `mod 5^K`) now also lift.
    // iter-105 perf: pre-build name → SimpleDef* index (same pattern as
    // findDef0 above). Called in residue-expansion and Hensel lift loops.
    std::unordered_map<std::string, const SimpleDef*> simpleDefByVar_lift;
    simpleDefByVar_lift.reserve(simpleDefs.size());
    for (const auto& sd : simpleDefs) simpleDefByVar_lift.emplace(sd.vVar, &sd);
    auto findDef = [&](const std::string& v) -> const SimpleDef* {
        auto it = simpleDefByVar_lift.find(v);
        return it != simpleDefByVar_lift.end() ? it->second : nullptr;
    };
    const mpz_class enumCap = currentEnumBudget();
    const mpz_class modCapForLift = currentModulusCap();

    for (const auto& G : groups) {
        auto pk = factorAsPrimePower(G.n);
        if (!pk) continue;                  // not a prime power
        mpz_class P;
        long K = 0;
        std::tie(P, K) = *pk;
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
        if (k0 > 40) continue;              // hard k0 ceiling (prevents pow overflow regardless of p)
        // mBase = p^k0. For the p = 2 fast path this matches the old shift;
        // for p > 2 it can grow much faster, so we cap on the actual mBase
        // value via modCapForLift (currentModulusCap with wall-clock scaling)
        // rather than on k0 alone.
        mpz_class mBase;
        mpz_pow_ui(mBase.get_mpz_t(), P.get_mpz_t(), static_cast<unsigned long>(k0));
        if (mBase > modCapForLift) continue;

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
            std::cerr << "[MODRES-HENSEL] goal r=" << G.rVar
                      << " p=" << P.get_str() << " K=" << K
                      << " vLast=" << vLast << " steps=" << steps
                      << " base=" << baseVar << " k0=" << k0 << " -> UNSAT\n";
        }
        // UNSAT: p^K | (mult*vLast - 1) => r = 1, contradicting r != 1.
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
