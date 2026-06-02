#include "theory/arith/nra/StructuralIntegerProbe.h"
#include <algorithm>
#include <vector>
#include <unordered_set>
#include <string>
#include <map>
#include <fstream>
#include <cstdlib>

namespace xolver {

namespace {

// Candidate value sets — small integers + dyadic rationals.
// Order matters: integers first (z3 nlsat prefers integers), then halves,
// then powers of 2 down to 1/2^20 (mgc-class denominators).
static const std::vector<mpq_class>& integerCandidates() {
    static const std::vector<mpq_class> values = {
        mpq_class(1), mpq_class(2), mpq_class(3),
        mpq_class(4), mpq_class(8),
        mpq_class(1, 2), mpq_class(3, 2),
    };
    return values;
}

// Larger candidate set used for FILL of non-structural vars when
// the simple integer attempt fails. Power-of-2 denominators target
// dyadic-refinement model styles (mgc_09: theta=1/256, alpha=1/2^19).
static const std::vector<mpq_class>& dyadicCandidates() {
    static const std::vector<mpq_class> values = {
        mpq_class(1), mpq_class(2), mpq_class(3), mpq_class(4),
        mpq_class(1, 2), mpq_class(1, 4), mpq_class(1, 8),
        mpq_class(1, 16), mpq_class(1, 32), mpq_class(1, 64),
        mpq_class(1, 128), mpq_class(1, 256), mpq_class(1, 1024),
    };
    return values;
}

// Compute the maximum exponent of each variable across all constraints.
std::vector<std::pair<VarId, int>> rankVarsByMaxExponent(
    const std::vector<StructuralIntegerProbe::Constraint>& constraints,
    PolynomialKernel& kernel) {

    std::unordered_map<VarId, int> maxExp;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;
        for (const auto& term : *termsOpt) {
            for (const auto& [vid, exp] : term.powers) {
                auto it = maxExp.find(vid);
                if (it == maxExp.end() || it->second < exp) {
                    maxExp[vid] = exp;
                }
            }
        }
    }
    std::vector<std::pair<VarId, int>> ranked(maxExp.begin(), maxExp.end());
    std::sort(ranked.begin(), ranked.end(),
              [](const auto& a, const auto& b) { return a.second > b.second; });
    return ranked;
}

// Sound evaluation: every active constraint holds under the candidate model.
// Defensive: 0-fill any var in a constraint's poly that's missing from the model
// (matches the existing validateCandidate pattern in NraSolver).
bool validates(const std::vector<StructuralIntegerProbe::Constraint>& constraints,
               PolynomialKernel& kernel,
               const std::unordered_map<VarId, mpq_class>& model) {
    std::unordered_map<std::string, mpq_class> evalModel;
    evalModel.reserve(model.size());
    for (const auto& [v, q] : model) {
        evalModel.emplace(std::string(kernel.varName(v)), q);
    }
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) return false;
        std::unordered_map<std::string, mpq_class> em = evalModel;
        for (const auto& vn : kernel.variables(c.poly)) {
            em.emplace(vn, mpq_class(0));
        }
        const int s = kernel.sgn(c.poly, em);
        bool ok = false;
        switch (c.rel) {
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

// Propagation pass: given a partial pinning + set of sign-pinned-positive vars,
// walk each Eq constraint, substitute pinned vars, factor out positive
// sign-pinned common factors (sign-aware division by Q > 0 reduces P=0 to R=0
// where P = Q*R), and derive any single-variable forced bindings (degree-1
// univariate or constant-must-be-zero).
//
// Returns the augmented pinning, or nullopt on detected infeasibility for
// this branch (a constant residual that doesn't equal 0, or a univariate
// derivation that gives a non-positive value when the var is sign-pinned).
//
// Implementation is one-pass over each constraint with a fixpoint loop;
// each iteration may add bindings that enable further factor-and-derive.
std::optional<std::unordered_map<VarId, mpq_class>> propagateForcedBindings(
    const std::vector<StructuralIntegerProbe::Constraint>& constraints,
    PolynomialKernel& kernel,
    const std::unordered_map<VarId, mpq_class>& initial,
    const std::unordered_set<VarId>& signPinnedPositive) {

    std::unordered_map<VarId, mpq_class> pinned = initial;
    bool changed = true;
    int rounds = 0;
    constexpr int kMaxRounds = 12;
    while (changed && rounds++ < kMaxRounds) {
        changed = false;
        for (const auto& c : constraints) {
            if (c.rel != Relation::Eq) continue;
            if (c.poly == NullPoly) continue;

            // Substitute all currently-pinned vars into the polynomial.
            PolyId p = c.poly;
            bool ok = true;
            for (const auto& [v, val] : pinned) {
                auto next = kernel.substituteRational(p, v, val);
                if (!next) { ok = false; break; }
                p = *next;
            }
            if (!ok) continue;

            auto termsOpt = kernel.terms(p);
            if (!termsOpt) continue;
            const auto& terms = *termsOpt;
            if (terms.empty()) continue;

            // Identify free vars in the residual (post-substitution).
            std::unordered_set<VarId> freeVars;
            for (const auto& t : terms) {
                for (const auto& [v, e] : t.powers) freeVars.insert(v);
            }

            // CASE 1 — residual is constant: relation must hold.
            if (freeVars.empty()) {
                bool nonzero = false;
                for (const auto& t : terms) if (t.coefficient != 0) { nonzero = true; break; }
                if (nonzero) return std::nullopt;  // const != 0 with Eq → infeasible
                continue;
            }

            // CASE 2 — monomial-GCD across all terms is a product of
            // sign-pinned-positive vars. Divide out, derive R = 0.
            std::map<VarId, int> gcd;
            bool gcdInit = false;
            for (const auto& t : terms) {
                if (t.coefficient == 0) continue;
                std::map<VarId, int> tp;
                for (const auto& [v, e] : t.powers) tp[v] = e;
                if (!gcdInit) { gcd = std::move(tp); gcdInit = true; continue; }
                std::map<VarId, int> next;
                for (const auto& [v, e] : gcd) {
                    auto it = tp.find(v);
                    if (it != tp.end()) next[v] = std::min(e, it->second);
                }
                gcd = std::move(next);
                if (gcd.empty()) break;
            }
            // Check every gcd factor is sign-pinned positive.
            bool factorIsPositive = !gcd.empty();
            for (const auto& [v, e] : gcd) {
                (void)e;
                if (!signPinnedPositive.count(v)) { factorIsPositive = false; break; }
            }
            if (!factorIsPositive) {
                // Skip (gcd contains a sign-unknown factor; can't divide).
            }

            // Build R = P / Q where Q is the GCD monomial. Then proceed
            // on R for univariate derivation.
            std::vector<PolynomialKernel::MonomialTerm> rTerms;
            if (factorIsPositive) {
                rTerms.reserve(terms.size());
                for (const auto& t : terms) {
                    if (t.coefficient == 0) continue;
                    PolynomialKernel::MonomialTerm r;
                    r.coefficient = t.coefficient;
                    std::map<VarId, int> tp;
                    for (const auto& [v, e] : t.powers) tp[v] = e;
                    for (const auto& [v, e] : gcd) tp[v] -= e;
                    for (const auto& [v, e] : tp) {
                        if (e > 0) r.powers.push_back({v, e});
                    }
                    rTerms.push_back(std::move(r));
                }
            } else {
                rTerms.assign(terms.begin(), terms.end());
            }

            // CASE 3 — residual R is univariate degree-1 in some var v.
            //   coeff * v + const = 0  ⇒  v = -const / coeff.
            std::unordered_set<VarId> rFree;
            for (const auto& t : rTerms) {
                for (const auto& [v, e] : t.powers) rFree.insert(v);
            }
            if (rFree.size() == 1) {
                VarId v = *rFree.begin();
                mpz_class coeff(0), constTerm(0);
                bool simple = true;
                for (const auto& t : rTerms) {
                    if (t.coefficient == 0) continue;
                    if (t.powers.empty()) {
                        constTerm += t.coefficient;
                    } else if (t.powers.size() == 1 && t.powers[0].first == v &&
                               t.powers[0].second == 1) {
                        coeff += t.coefficient;
                    } else {
                        // Higher degree or different shape → not simple linear.
                        simple = false;
                        break;
                    }
                }
                if (simple && coeff != 0) {
                    mpq_class derived(-constTerm, coeff);
                    derived.canonicalize();
                    auto it = pinned.find(v);
                    if (it == pinned.end()) {
                        // New binding.
                        if (signPinnedPositive.count(v) && derived <= 0) {
                            return std::nullopt;  // contradicts positivity
                        }
                        pinned[v] = derived;
                        changed = true;
                    } else if (it->second != derived) {
                        return std::nullopt;  // conflicting bindings
                    }
                }
            }
        }
    }
    return pinned;
}

} // namespace

std::optional<std::unordered_map<VarId, mpq_class>>
StructuralIntegerProbe::tryProbe(
    const std::vector<Constraint>& constraints,
    PolynomialKernel& kernel,
    int maxStructuralVars,
    int maxBudget) {

    if (constraints.empty()) return std::nullopt;

    // Detect sign-pinned-positive vars: constraints of shape
    //   `var > 0`  ≡  `-var < 0`  ≡  poly = -var, rel = Lt
    //   `var ≥ ε` for ε > 0 reduces here too.
    // Captured for the propagation pass's sign-aware factoring division.
    std::unordered_set<VarId> positiveVars;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        if (c.rel != Relation::Lt && c.rel != Relation::Leq &&
            c.rel != Relation::Gt && c.rel != Relation::Geq) continue;
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt || termsOpt->size() != 1) continue;
        const auto& t = (*termsOpt)[0];
        if (t.powers.size() != 1 || t.powers[0].second != 1) continue;
        VarId v = t.powers[0].first;
        // `-v < 0` ⇒ v > 0;  `-v <= 0` ⇒ v ≥ 0 (treat as positive for our use);
        // `v > 0` directly.
        bool isPos = false;
        if (c.rel == Relation::Lt && t.coefficient < 0) isPos = true;
        if (c.rel == Relation::Leq && t.coefficient < 0) isPos = true;
        if (c.rel == Relation::Gt && t.coefficient > 0) isPos = true;
        if (c.rel == Relation::Geq && t.coefficient > 0) isPos = true;
        if (isPos) positiveVars.insert(v);
    }

    // Rank vars by max exponent (high-degree vars are likely "structural"
    // in the mgc-class sense: their values force everything else via the
    // substitution chain in eq1, eq2, eq3).
    auto ranked = rankVarsByMaxExponent(constraints, kernel);
    if (ranked.empty()) return std::nullopt;

    // Collect ALL vars seen across constraints, so we can fill the
    // non-structural ones with default values.
    std::unordered_set<VarId> allVars;
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        for (const auto& vn : kernel.variables(c.poly)) {
            auto vidOpt = kernel.findVar(vn);
            if (vidOpt) allVars.insert(*vidOpt);
        }
    }
    if (allVars.empty()) return std::nullopt;

    // Pick top-K structural vars (by max-exponent).
    std::vector<VarId> structural;
    for (const auto& [vid, exp] : ranked) {
        if (static_cast<int>(structural.size()) >= maxStructuralVars) break;
        // Only consider vars whose max exponent is >= 2 (degree-1 vars are
        // typically parameters, not structural choices).
        if (exp < 2) break;
        structural.push_back(vid);
    }
    if (structural.empty()) return std::nullopt;

    // Other vars get a default fill candidate.
    std::vector<VarId> nonStructural;
    for (VarId v : allVars) {
        if (std::find(structural.begin(), structural.end(), v) == structural.end()) {
            nonStructural.push_back(v);
        }
    }

    const auto& structCands = integerCandidates();
    const auto& fillCands = dyadicCandidates();

    int trials = 0;

    // Enumerate cartesian product of structural-var assignments.
    std::vector<size_t> structIdx(structural.size(), 0);
    while (true) {
        // For each structural assignment, sweep non-structural defaults.
        // To keep it tractable, fix non-structural vars at index 0 first
        // (all 1s), then try other dyadic candidates for non-structural
        // vars ONE AT A TIME (single-flip sweep).
        if (++trials > maxBudget) return std::nullopt;

        // Step A — Pin structural vars only (no defaults yet).
        std::unordered_map<VarId, mpq_class> initial;
        for (size_t i = 0; i < structural.size(); ++i) {
            initial.emplace(structural[i], structCands[structIdx[i]]);
        }

        // Step B — Run propagation: factor + sign-aware divide derives
        // forced bindings (mgc-class: vv3=2 → gamma0=513 → vv2=2 → ...).
        auto propagated = propagateForcedBindings(constraints, kernel,
                                                   initial, positiveVars);
        // Diag: how many bindings were derived?
        // Diag only on each new structural pinning (skip the single-flip
        // sub-trials so the log stays readable).
        if (std::getenv("XOLVER_NRA_INT_PROBE_DIAG")) {
            std::ofstream dst("/tmp/int_probe.txt", std::ios::app);
            dst << "[INT-PROBE] trial=" << trials
                << " structural={";
            for (auto& [v, q] : initial) dst << kernel.varName(v) << "=" << q.get_str() << " ";
            dst << "} prop=";
            if (!propagated) dst << "INFEASIBLE";
            else {
                dst << propagated->size() << " bindings: ";
                for (auto& [v, q] : *propagated) dst << kernel.varName(v) << "=" << q.get_str() << " ";
            }
            dst << "\n";
            dst.flush();
        }
        if (!propagated) {
            // Branch infeasible (constant !=0 or contradiction). Skip.
            // Advance below; continue normally.
        }

        // Step C — Build full model: propagation bindings, plus defaults
        // (1) for remaining free vars.
        std::unordered_map<VarId, mpq_class> base;
        if (propagated) base = *propagated; else base = initial;
        for (VarId v : allVars) {
            base.emplace(v, mpq_class(1));
        }

        if (validates(constraints, kernel, base)) return base;

        // Single-flip sweep over non-structural vars and fill candidates.
        // Skip vars that propagation already pinned (they have a forced value
        // — flipping them would contradict the substitution chain).
        std::unordered_set<VarId> pinnedFromProp;
        if (propagated) {
            for (const auto& [v, _] : *propagated) pinnedFromProp.insert(v);
        }
        for (VarId v : nonStructural) {
            if (pinnedFromProp.count(v)) continue;
            for (const auto& cand : fillCands) {
                if (++trials > maxBudget) return std::nullopt;
                if (cand == mpq_class(1)) continue;
                auto try_ = base;
                try_[v] = cand;
                if (validates(constraints, kernel, try_)) return try_;
            }
        }

        // Advance structural-var index (cartesian).
        size_t carry = 0;
        for (; carry < structural.size(); ++carry) {
            structIdx[carry]++;
            if (structIdx[carry] < structCands.size()) break;
            structIdx[carry] = 0;
        }
        if (carry == structural.size()) break;  // exhausted
    }

    return std::nullopt;
}

} // namespace xolver
