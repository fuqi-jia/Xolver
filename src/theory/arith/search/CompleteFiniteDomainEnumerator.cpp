#include "theory/arith/search/CompleteFiniteDomainEnumerator.h"

#include <algorithm>
#include <set>

namespace zolver {

namespace {

// Evaluate substitution definitions at a (partial) rational assignment of the
// free variables, resolving substituted-var dependency chains.  Returns false
// if some substituted var cannot be reduced to a constant (gating failure).
bool resolveAssignment(const PresolveState& st,
                       std::map<VarId, mpq_class>& assign /* free vars in */) {
    size_t remaining = st.substMap.size();
    for (size_t iter = 0; iter <= st.substMap.size() + 1 && remaining > 0; ++iter) {
        bool progress = false;
        for (const auto& [v, entry] : st.substMap) {
            if (assign.count(v)) continue;
            RationalPolynomial t = entry.value;
            for (const auto& [var, val] : assign) {
                if (t.contains(var)) t = t.substituteRational(var, val);
            }
            if (t.isConstant()) {
                assign[v] = t.constantValue();
                --remaining;
                progress = true;
            }
        }
        if (!progress) break;
    }
    return remaining == 0;
}

}  // namespace

FiniteDomainResult CompleteFiniteDomainEnumerator::run(
    const PresolveState& st,
    const std::vector<NormalizedNiaConstraint>& normalized,
    const IntegerModelValidator& validator,
    PolynomialKernel& kernel) {

    FiniteDomainResult res;
    if (!st.integerDomain) return res;  // NIA only

    // Collect all original variables from the active constraints.
    std::set<VarId> vars;
    for (const auto& c : normalized) {
        for (const auto& name : kernel.variables(c.poly)) {
            if (auto v = kernel.findVar(name)) vars.insert(*v);
        }
    }
    if (vars.empty()) return res;

    // Partition into free (finite Int bound, not substituted) vs substituted.
    std::vector<VarId> freeVars;
    for (VarId v : vars) {
        if (st.substMap.count(v)) continue;  // substituted → reconstructed
        auto it = st.bounds.find(v);
        if (it != st.bounds.end() && it->second.set.isFiniteInt()) {
            freeVars.push_back(v);
        } else {
            return res;  // unbounded & un-substituted → NotApplicable
        }
    }

    // Per-free-var integer points + product-size gate.
    std::vector<std::vector<mpz_class>> points;
    size_t product = 1;
    for (VarId v : freeVars) {
        auto pts = st.bounds.at(v).set.integerPoints();
        if (pts.empty()) {
            // No integer in a free var's domain ⇒ vacuously unsatisfiable.
            // (addBound would normally have caught this; defensive.)
            return res;
        }
        product *= pts.size();
        if (product > kMaxFiniteDomainSize) return res;
        points.push_back(std::move(pts));
    }

    // Cartesian sweep.
    std::vector<size_t> idx(freeVars.size(), 0);
    bool any = !freeVars.empty() || !st.substMap.empty();
    if (!any) return res;

    bool anyIndeterminate = false;

    while (true) {
        std::map<VarId, mpq_class> assign;
        for (size_t i = 0; i < freeVars.size(); ++i) assign[freeVars[i]] = mpq_class(points[i][idx[i]]);

        bool resolved = resolveAssignment(st, assign);
        bool allInt = resolved;
        if (resolved) {
            for (const auto& [v, val] : assign) {
                (void)v;
                if (val.get_den() != 1) { allInt = false; break; }
            }
        }
        if (resolved && allInt) {
            IntegerModel model;
            for (const auto& [v, val] : assign) model[std::string(kernel.varName(v))] = val.get_num();
            auto vres = validator.validate(model, normalized);
            if (vres == IntegerModelValidator::Result::Valid) {
                res.status = FiniteDomainResult::Status::Sat;
                res.model = std::move(model);
                return res;
            }
            if (vres == IntegerModelValidator::Result::Indeterminate) {
                anyIndeterminate = true;
            }
            // Violated → continue enumeration
        } else {
            // Could not resolve substituted vars or non-integer assignment.
            // Cannot validate this candidate → treat as indeterminate.
            anyIndeterminate = true;
        }

        // advance odometer
        int k = static_cast<int>(freeVars.size()) - 1;
        while (k >= 0) {
            if (++idx[k] < points[k].size()) break;
            idx[k] = 0;
            --k;
        }
        if (k < 0) break;  // exhausted
        if (freeVars.empty()) break;  // single (substituted-only) candidate
    }

    // If any candidate was indeterminate (could not be validated), we cannot
    // soundly claim UNSAT — the missing validation might have been a SAT.
    if (anyIndeterminate) {
        return res;  // NotApplicable
    }

    // Exhausted with every candidate explicitly Violated ⇒ complete UNSAT.
    std::vector<SatLit> clause;
    for (const auto& c : normalized) clause.push_back(c.reason);
    for (VarId v : freeVars) {
        const auto& rl = st.bounds.at(v).reasons.baseLiterals;
        clause.insert(clause.end(), rl.begin(), rl.end());
    }
    std::sort(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    clause.erase(std::unique(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), clause.end());

    res.status = FiniteDomainResult::Status::UnsatComplete;
    res.conflict = TheoryConflict{clause};
    return res;
}

} // namespace zolver
