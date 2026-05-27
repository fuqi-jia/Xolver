#include "theory/arith/nia/reasoners/GroebnerIdealReasoner.h"
#include <algorithm>
#include <map>
#include <set>

namespace xolver {

namespace {

// A monomial: variable -> exponent (>0), kept sorted by VarId.
using Mono = std::vector<std::pair<VarId, int>>;

struct LeadTerm { mpz_class coeff; Mono mono; bool valid = false; };

// Lexicographic monomial order with the SMALLEST VarId most significant.
// Admissible (1 is minimal, multiplicative), which is all Buchberger needs.
bool monoLess(const Mono& a, const Mono& b) {
    size_t i = 0, j = 0;
    while (i < a.size() || j < b.size()) {
        VarId va = (i < a.size()) ? a[i].first : VarId(UINT32_MAX);
        VarId vb = (j < b.size()) ? b[j].first : VarId(UINT32_MAX);
        VarId v = std::min(va, vb);
        int ea = (va == v) ? a[i].second : 0;
        int eb = (vb == v) ? b[j].second : 0;
        if (ea != eb) return ea < eb;
        if (va == v) ++i;
        if (vb == v) ++j;
    }
    return false;  // equal
}

bool monoDivides(const Mono& g, const Mono& f) {  // g | f ?
    for (const auto& [v, eg] : g) {
        auto it = std::find_if(f.begin(), f.end(), [&](auto& p){ return p.first == v; });
        if (it == f.end() || it->second < eg) return false;
    }
    return true;
}

Mono monoQuot(const Mono& f, const Mono& g) {  // f / g (assumes g | f)
    Mono q;
    for (const auto& [v, ef] : f) {
        int eg = 0;
        for (const auto& [vg, e] : g) if (vg == v) { eg = e; break; }
        if (ef - eg > 0) q.emplace_back(v, ef - eg);
    }
    return q;
}

Mono monoLcm(const Mono& a, const Mono& b) {
    std::map<VarId, int> m;
    for (const auto& [v, e] : a) m[v] = std::max(m[v], e);
    for (const auto& [v, e] : b) m[v] = std::max(m[v], e);
    Mono r(m.begin(), m.end());
    return r;
}

} // namespace

GroebnerIdealReasoner::GroebnerIdealReasoner(PolynomialKernel& kernel)
    : kernel_(kernel) {}

NiaReasoningResult GroebnerIdealReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints) {
    const NiaReasoningResult noChange{NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // Build the generator set from the equalities; collect their reasons.
    std::vector<PolyId> G;
    std::vector<SatLit> reasons;
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        if (!kernel_.terms(c.poly)) return noChange;  // need monomial decomposition
        if (kernel_.isZero(c.poly)) continue;
        G.push_back(c.poly);
        reasons.push_back(c.reason);
    }
    if (G.empty()) return noChange;

    // Size guard: Buchberger is exponential in #variables and O(g²)+ in the
    // number of generators g; on large equality systems (e.g. VeryMax: 20+
    // equalities over 50+ vars) it burns the whole time budget and REGRESSES
    // otherwise-fast cases (measured: a 22-eq/54-var sat case goes from <10s to
    // timeout). The 1∈ideal contradiction is also vanishingly unlikely in such
    // large systems. Restrict to small systems where it is cheap and useful.
    {
        std::set<std::string> vs;
        for (PolyId g : G) for (const auto& v : kernel_.variables(g)) vs.insert(v);
        if (G.size() > 6 || vs.size() > 8) return noChange;
    }

    auto monoOfTerm = [](const PolynomialKernel::MonomialTerm& t) -> Mono {
        Mono m(t.powers.begin(), t.powers.end());
        std::sort(m.begin(), m.end());
        return m;
    };
    auto leadTerm = [&](PolyId p) -> LeadTerm {
        auto ts = kernel_.terms(p);
        if (!ts || ts->empty()) return {};
        const PolynomialKernel::MonomialTerm* best = nullptr;
        Mono bestMono;
        for (const auto& t : *ts) {
            Mono m = monoOfTerm(t);
            if (!best || monoLess(bestMono, m)) { best = &t; bestMono = std::move(m); }
        }
        return {best->coefficient, bestMono, true};
    };
    auto monoToPoly = [&](const Mono& m) -> PolyId {
        PolyId p = kernel_.mkOne();
        for (const auto& [v, e] : m)
            for (int i = 0; i < e; ++i) p = kernel_.mul(p, kernel_.mkVar(v));
        return p;
    };
    auto totalDeg = [&](PolyId p) -> int {
        auto ts = kernel_.terms(p);
        int d = 0;
        if (ts) for (const auto& t : *ts) {
            int s = 0; for (auto& pr : t.powers) s += pr.second; d = std::max(d, s);
        }
        return d;
    };
    auto nonzeroConst = [&](PolyId p) -> bool {
        return kernel_.isConstant(p) && !kernel_.isZero(p);
    };

    // S-polynomial: LC(g)*(L/LTf)*f - LC(f)*(L/LTg)*g  (leading terms cancel; stays in ℤ).
    auto spoly = [&](PolyId f, PolyId g) -> PolyId {
        LeadTerm lf = leadTerm(f), lg = leadTerm(g);
        Mono L = monoLcm(lf.mono, lg.mono);
        PolyId tf = kernel_.mul(kernel_.mkConst(mpq_class(lg.coeff)), monoToPoly(monoQuot(L, lf.mono)));
        PolyId tg = kernel_.mul(kernel_.mkConst(mpq_class(lf.coeff)), monoToPoly(monoQuot(L, lg.mono)));
        return kernel_.sub(kernel_.mul(tf, f), kernel_.mul(tg, g));
    };

    // Pseudo-reduce f by the basis until no leading term divides (bounded steps).
    auto reduce = [&](PolyId f) -> PolyId {
        for (int step = 0; step < 400; ++step) {
            if (kernel_.isZero(f)) return f;
            LeadTerm lf = leadTerm(f);
            if (!lf.valid) return f;
            const PolyId* div = nullptr; LeadTerm lg;
            for (const auto& g : G) {
                LeadTerm cand = leadTerm(g);
                if (cand.valid && monoDivides(cand.mono, lf.mono)) { div = &g; lg = cand; break; }
            }
            if (!div) return f;  // reduced
            // f := LC(g)*f - LC(f)*(LTf/LTg)*g
            PolyId tg = kernel_.mul(kernel_.mkConst(mpq_class(lf.coeff)), monoToPoly(monoQuot(lf.mono, lg.mono)));
            f = kernel_.sub(kernel_.mul(kernel_.mkConst(mpq_class(lg.coeff)), f), kernel_.mul(tg, *div));
        }
        return f;  // step budget hit; caller only acts on a clean constant
    };

    auto refute = [&]() -> NiaReasoningResult {
        return {NiaReasoningKind::Conflict, TheoryConflict{reasons}, std::nullopt};
    };

    // A generator already a nonzero constant ⇒ 1 ∈ ideal.
    for (PolyId g : G) if (nonzeroConst(g)) return refute();

    // Bounded Buchberger.
    constexpr size_t MAX_BASIS = 48;
    constexpr int MAX_STEPS = 400;
    constexpr int MAX_DEG = 16;
    std::vector<std::pair<size_t, size_t>> pairs;
    for (size_t i = 0; i < G.size(); ++i)
        for (size_t j = i + 1; j < G.size(); ++j) pairs.emplace_back(i, j);

    int steps = 0;
    while (!pairs.empty()) {
        if (++steps > MAX_STEPS || G.size() > MAX_BASIS) return noChange;  // budget
        auto [i, j] = pairs.back(); pairs.pop_back();
        PolyId r = reduce(spoly(G[i], G[j]));
        if (kernel_.isZero(r)) continue;
        if (nonzeroConst(r)) return refute();           // 1 ∈ ideal ⇒ UNSAT
        if (totalDeg(r) > MAX_DEG) continue;             // keep it bounded (sound to skip)
        size_t ni = G.size();
        G.push_back(r);
        for (size_t k = 0; k < ni; ++k) pairs.emplace_back(k, ni);
    }
    return noChange;
}

} // namespace xolver
