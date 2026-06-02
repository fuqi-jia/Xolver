#include "theory/arith/nra/StructuralIntegerProbe.h"
#include <algorithm>
#include <vector>
#include <unordered_set>
#include <string>

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

} // namespace

std::optional<std::unordered_map<VarId, mpq_class>>
StructuralIntegerProbe::tryProbe(
    const std::vector<Constraint>& constraints,
    PolynomialKernel& kernel,
    int maxStructuralVars,
    int maxBudget) {

    if (constraints.empty()) return std::nullopt;

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

        // Build base model: structural vars from structIdx, non-structural
        // all = 1.
        std::unordered_map<VarId, mpq_class> base;
        for (size_t i = 0; i < structural.size(); ++i) {
            base.emplace(structural[i], structCands[structIdx[i]]);
        }
        for (VarId v : nonStructural) {
            base.emplace(v, mpq_class(1));
        }

        if (validates(constraints, kernel, base)) return base;

        // Single-flip sweep over non-structural vars and fill candidates.
        for (VarId v : nonStructural) {
            for (const auto& cand : fillCands) {
                if (++trials > maxBudget) return std::nullopt;
                if (cand == mpq_class(1)) continue;  // base already tried this
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
