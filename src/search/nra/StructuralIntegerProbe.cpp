#include "base/RuntimeConfig.h"
#include "search/nra/StructuralIntegerProbe.h"
#include "base/EnvParam.h"   // XOLVER_NRA_EQ_CASCADE_DYADIC_DEPTH
#include <algorithm>
#include <vector>
#include <unordered_set>
#include <string>
#include <map>
#include <fstream>
#include <cstdlib>
#include <functional>

namespace xolver {

namespace {

// Detect sign-pinned-positive vars (`v > 0` / `v >= 0` shaped atoms). Shared by
// the equality-cascade solver.
std::unordered_set<VarId> detectPositiveVars(
    const std::vector<StructuralIntegerProbe::Constraint>& constraints,
    PolynomialKernel& kernel) {
    std::unordered_set<VarId> pos;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        if (c.rel != Relation::Lt && c.rel != Relation::Leq &&
            c.rel != Relation::Gt && c.rel != Relation::Geq) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt || termsOpt->size() != 1) continue;
        const auto& t = (*termsOpt)[0];
        if (t.powers.size() != 1 || t.powers[0].second != 1) continue;
        VarId v = t.powers[0].first;
        bool isPos = false;
        if ((c.rel == Relation::Lt || c.rel == Relation::Leq) && t.coefficient < 0) isPos = true;
        if ((c.rel == Relation::Gt || c.rel == Relation::Geq) && t.coefficient > 0) isPos = true;
        if (isPos) pos.insert(v);
    }
    return pos;
}

// Candidate values for a generator. High-degree "leaf" vars (the exponent
// bases, e.g. vv3 with vv3^16) must be small or their powers explode, so they
// get small integers. Lower-degree "parameter" vars (alpha/theta-style) often
// need fine dyadic values (mgc models reach 1/2^17, 1/2^9), so they get a
// power-of-two ladder 1, 1/2, …, 1/2^kDeep (index k = 1/2^k) then 2, 3.
std::vector<mpq_class> cascadeCandidates(bool isLeaf, int kDeep) {
    // Non-deep generators (the top exponent base + linear params): small
    // MAGNITUDE values, both integer and a couple of dyadics. Small values never
    // explode a high power (only large bases do), so 1/2, 1/4 are safe and let a
    // top variable take a small dyadic when needed.
    if (isLeaf) return { mpq_class(1), mpq_class(2), mpq_class(3),
                         mpq_class(1, 2), mpq_class(1, 4) };
    std::vector<mpq_class> v;
    v.reserve(kDeep + 3);
    for (int k = 0; k <= kDeep; ++k)
        v.push_back(mpq_class(mpz_class(1), mpz_class(1) << k));  // 1/2^k (k=0 ⇒ 1)
    v.push_back(mpq_class(2));
    v.push_back(mpq_class(3));
    return v;
}

// ---- numeric (libpoly-free) term representation for the hot enumeration loop --
// Working with extracted mpq terms avoids creating kernel polynomials per combo
// (which accumulate in the hash-consed pool → multi-GB bloat). Pure rational.
struct NTerm {
    mpq_class coeff;
    std::vector<std::pair<VarId, int>> powers;
};
struct NConstraint {
    std::vector<NTerm> terms;
    Relation rel;
};

mpq_class qpow(const mpq_class& base, int e) {
    mpq_class r(1);
    for (int i = 0; i < e; ++i) r *= base;
    return r;
}

// Evaluate a numeric polynomial at a (total) rational assignment.
mpq_class evalNPoly(const std::vector<NTerm>& terms,
                    const std::unordered_map<VarId, mpq_class>& asg) {
    mpq_class s(0);
    for (const auto& t : terms) {
        mpq_class m = t.coeff;
        for (const auto& [v, e] : t.powers) {
            auto it = asg.find(v);
            if (it == asg.end()) { m = 0; break; }   // unassigned ⇒ treat term as 0-safe
            m *= qpow(it->second, e);
        }
        s += m;
    }
    return s;
}

// Cascade-derive the non-generator (degree-1) variables from the equalities,
// given a full generator assignment. Each equality, once the generators and any
// already-derived variables are substituted, must be linear in a single
// remaining unknown ⇒ solve it; iterate to fixpoint. Returns the completed
// assignment, or nullopt if some variable stays underivable / a positivity
// constraint is violated.
std::optional<std::unordered_map<VarId, mpq_class>> cascadeDerive(
    const std::vector<NConstraint>& ncons,
    const std::unordered_map<VarId, mpq_class>& genAssign,
    const std::unordered_set<VarId>& derivedVars,
    const std::unordered_set<VarId>& positiveVars) {

    std::unordered_map<VarId, mpq_class> known = genAssign;
    std::unordered_set<VarId> remaining = derivedVars;
    bool progress = true;
    while (progress && !remaining.empty()) {
        progress = false;
        for (const auto& nc : ncons) {
            if (nc.rel != Relation::Eq) continue;
            // Determine the unknown variables this equality is (currently) linear in.
            std::unordered_set<VarId> unk;
            bool linear = true;
            for (const auto& t : nc.terms) {
                int unkCount = 0, unkExp = 0; VarId uv = NullVar;
                for (const auto& [v, e] : t.powers) {
                    if (remaining.count(v)) { ++unkCount; unkExp += e; uv = v; }
                }
                if (unkCount >= 1) {
                    if (unkCount > 1 || unkExp > 1) { linear = false; break; }
                    unk.insert(uv);
                }
            }
            if (!linear || unk.size() != 1) continue;
            VarId u = *unk.begin();
            // coeff·u + const = 0 (all non-u vars are known here).
            mpq_class coeffU(0), constT(0);
            for (const auto& t : nc.terms) {
                mpq_class val = t.coeff;
                bool hasU = false;
                for (const auto& [v, e] : t.powers) {
                    if (v == u) { hasU = true; continue; }   // u appears to power 1
                    val *= qpow(known.at(v), e);
                }
                (hasU ? coeffU : constT) += val;
            }
            if (coeffU == 0) continue;   // not solvable for u from this equality now
            mpq_class uval = -constT / coeffU;
            uval.canonicalize();
            if (positiveVars.count(u) && uval <= 0) return std::nullopt;  // violates positivity
            known[u] = uval;
            remaining.erase(u);
            progress = true;
        }
    }
    if (!remaining.empty()) return std::nullopt;   // not a total model
    return known;
}

// Exact numeric validation of every original constraint at the full assignment.
bool validatesNumeric(const std::vector<NConstraint>& ncons,
                      const std::unordered_map<VarId, mpq_class>& asg) {
    for (const auto& nc : ncons) {
        const mpq_class val = evalNPoly(nc.terms, asg);
        const int s = (val > 0) ? 1 : (val < 0 ? -1 : 0);
        bool ok = false;
        switch (nc.rel) {
            case Relation::Eq:  ok = (s == 0); break;
            case Relation::Geq: ok = (s >= 0); break;
            case Relation::Leq: ok = (s <= 0); break;
            case Relation::Gt:  ok = (s > 0);  break;
            case Relation::Lt:  ok = (s < 0);  break;
            case Relation::Neq: ok = (s != 0); break;
        }
        if (!ok) return false;
    }
    return true;
}

} // namespace

std::optional<std::unordered_map<VarId, mpq_class>>
StructuralIntegerProbe::trySolveCascade(
    const std::vector<Constraint>& constraints,
    PolynomialKernel& kernel,
    int maxBudget) {

    if (constraints.empty()) return std::nullopt;

    const std::unordered_set<VarId> positiveVars =
        detectPositiveVars(constraints, kernel);

    // Extract numeric terms ONCE (no kernel polynomials are created in the hot
    // loop ⇒ no hash-cons pool bloat), and collect max-degree + the var set.
    std::vector<NConstraint> ncons;
    ncons.reserve(constraints.size());
    std::unordered_map<VarId, int> maxDeg;
    std::unordered_set<VarId> allVars;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) return std::nullopt;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) return std::nullopt;
        NConstraint nc; nc.rel = c.rel;
        nc.terms.reserve(termsOpt->size());
        for (const auto& t : *termsOpt) {
            NTerm nt; nt.coeff = mpq_class(t.coefficient); nt.powers = t.powers;
            for (const auto& [v, e] : t.powers) {
                allVars.insert(v);
                auto it = maxDeg.find(v);
                if (it == maxDeg.end() || it->second < e) maxDeg[v] = e;
            }
            nc.terms.push_back(std::move(nt));
        }
        ncons.push_back(std::move(nc));
    }
    if (allVars.empty()) return std::nullopt;

    // Generators = variables of degree >= 2 in some constraint (they cannot be
    // solved by a degree-1 cascade, so they must be assigned). The rest are the
    // degree-1 "derived" variables the cascade computes (gamma0, vv2, lambda1, …).
    std::vector<VarId> gens;
    std::unordered_set<VarId> genSet;
    for (const auto& [v, d] : maxDeg) if (d >= 2) { gens.push_back(v); genSet.insert(v); }
    if (gens.empty()) return std::nullopt;
    if (gens.size() > 7) return std::nullopt;   // only mgc-shaped (small) systems
    std::unordered_set<VarId> derivedVars;
    for (VarId v : allVars) if (!genSet.count(v)) derivedVars.insert(v);

    // Pick the top variable (highest degree — the exponent base, e.g. vv3) and
    // classify the OTHER generators. A generator needs the fine dyadic ladder
    // ("deep") iff it appears SQUARED in a monomial alongside a near-top power
    // of the top variable: such a term (e.g. 6561·alpha²·vv3^16) blows eq_big up
    // unless that variable is tiny, so the model uses values like 1/2^17. A
    // variable only present linearly with high powers (delta·theta·vv3^18) can
    // stay O(1) and gets the small integer set. The top variable itself gets
    // small integers (large bases explode its own high power).
    int topDeg = 0; VarId topVar = NullVar;
    for (VarId v : gens) if (maxDeg[v] > topDeg) { topDeg = maxDeg[v]; topVar = v; }
    const int kNearTop = std::max(2, topDeg - 2);

    std::unordered_map<VarId, bool> deepMap;
    for (VarId g : gens) {
        bool isDeep = false;
        if (g != topVar) {
            for (const auto& nc : ncons) {
                for (const auto& t : nc.terms) {
                    int eg = 0, etop = 0;
                    for (const auto& [v, e] : t.powers) {
                        if (v == g) eg = e;
                        else if (v == topVar) etop = e;
                    }
                    if (eg >= 2 && etop >= kNearTop) { isDeep = true; break; }
                }
                if (isDeep) break;
            }
        }
        deepMap[g] = isDeep;
    }

    // Small-cardinality generators (top var + linear params) loop outermost so
    // every value is reached within budget; deep dyadic params loop innermost.
    std::stable_sort(gens.begin(), gens.end(), [&](VarId a, VarId b) {
        if (deepMap[a] != deepMap[b]) return !deepMap[a];   // non-deep (small) first
        return maxDeg[a] > maxDeg[b];
    });

    const int kDeep = [] {
        int v = config::read<config::ReadKind::Int>("XOLVER_NRA_EQ_CASCADE_DYADIC_DEPTH", 20);
        return (v > 0 && v <= 64) ? v : 20;
    }();
    std::vector<std::vector<mpq_class>> cands;
    cands.reserve(gens.size());
    for (VarId v : gens) cands.push_back(cascadeCandidates(/*isLeaf=*/!deepMap[v], kDeep));

    const bool diag = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_NRA_EQ_CASCADE_DIAG");
    if (diag) {
        std::ofstream d("/tmp/eq_cascade.txt", std::ios::app);
        d << "[EQ-CASCADE] vars=" << allVars.size() << " gens=" << gens.size()
          << " topVar=" << (topVar == NullVar ? std::string("?")
                                              : std::string(kernel.varName(topVar)))
          << " topDeg=" << topDeg << " budget=" << maxBudget << "\n";
        for (size_t i = 0; i < gens.size(); ++i)
            d << "    gen " << kernel.varName(gens[i]) << " maxDeg=" << maxDeg[gens[i]]
              << " deep=" << deepMap[gens[i]] << " cands=" << cands[i].size() << "\n";
        d.flush();
    }

    std::optional<std::unordered_map<VarId, mpq_class>> answer;
    long trials = 0;
    std::unordered_map<VarId, mpq_class> assign;

    // Cartesian enumeration of generator values; at a full assignment, derive
    // the linear tail and validate exactly.
    std::function<void(size_t)> sweep = [&](size_t gi) {
        if (answer || trials > maxBudget) return;
        if (gi == gens.size()) {
            ++trials;
            auto full = cascadeDerive(ncons, assign, derivedVars, positiveVars);
            if (!full) return;
            // Cheap pre-filter: the equalities are 0 by construction (the cascade
            // solved each derived var from one of them), so check the strict
            // inequalities FIRST and skip the expensive high-degree equality
            // re-evaluation on the overwhelming majority of non-models.
            for (const auto& nc : ncons) {
                if (nc.rel == Relation::Eq) continue;
                const mpq_class v = evalNPoly(nc.terms, *full);
                const int s = (v > 0) ? 1 : (v < 0 ? -1 : 0);
                bool ok = (nc.rel == Relation::Geq) ? (s >= 0)
                        : (nc.rel == Relation::Leq) ? (s <= 0)
                        : (nc.rel == Relation::Gt)  ? (s > 0)
                        : (nc.rel == Relation::Lt)  ? (s < 0)
                        : (nc.rel == Relation::Neq) ? (s != 0) : true;
                if (!ok) return;
            }
            // Inequalities hold: full exact validation over ALL constraints
            // (invariant 1) — confirms the equalities too.
            if (validatesNumeric(ncons, *full)) answer = std::move(full);
            return;
        }
        VarId v = gens[gi];
        for (const mpq_class& val : cands[gi]) {
            if (positiveVars.count(v) && val <= 0) continue;
            assign[v] = val;
            sweep(gi + 1);
            if (answer || trials > maxBudget) { assign.erase(v); return; }
        }
        assign.erase(v);
    };

    sweep(0);
    if (diag) {
        std::ofstream d("/tmp/eq_cascade.txt", std::ios::app);
        d << "[EQ-CASCADE] trials=" << trials
          << " result=" << (answer ? "SAT" : "none") << "\n";
        if (answer) for (const auto& [v, q] : *answer)
            d << "      " << kernel.varName(v) << " = " << q.get_str() << "\n";
        d.flush();
    }
    return answer;
}

} // namespace xolver
