#include "proof/BoolClausalProof.h"

#include <unordered_map>

namespace xolver {
namespace proof {

#ifdef XOLVER_ENABLE_PROOFS

namespace {
// Render a signed SAT literal as its SMT-LIB term, negating with `not`.
std::optional<std::string> renderLit(int lit, const std::vector<std::string>& varTerm) {
    int v = lit < 0 ? -lit : lit;
    if (v <= 0 || static_cast<size_t>(v) >= varTerm.size() || varTerm[v].empty())
        return std::nullopt;
    if (lit < 0) return "(not " + varTerm[v] + ")";
    return varTerm[v];
}
}  // namespace

std::optional<AletheProof> buildClausalRefutation(
    const std::vector<ClausalAssertion>& assertions,
    const std::vector<LratStep>& lrat,
    const std::vector<std::string>& varTerm) {
    if (assertions.empty() || lrat.empty()) return std::nullopt;

    AletheProof proof;

    // 1. Assume every assertion up front (the `.smt2` asserts them all, and the
    //    refutation's premises must be a subset). assumeId[k] is the id of the
    //    assume for assertions[k].
    std::vector<std::string> assumeId;
    assumeId.reserve(assertions.size());
    for (const auto& a : assertions) assumeId.push_back(proof.assume(a.smtText));

    // 2. Walk the LRAT in emission order. Map each SAT clause-id to the Alethe
    //    step (or assume) that proves it, so antecedent chains resolve to ids.
    std::unordered_map<int64_t, std::string> idToStep;
    size_t origCount = 0;
    bool sawEmpty = false;

    for (const auto& s : lrat) {
        if (s.original) {
            // The k-th original input clause is assertions[k]'s clause.
            if (origCount >= assertions.size()) return std::nullopt;
            const auto& a = assertions[origCount];
            const std::string& hId = assumeId[origCount];
            ++origCount;
            if (a.isUnit) {
                // The assume itself is the unit clause — no `or` step needed.
                idToStep[s.id] = hId;
            } else {
                // Clausify `(or t1..tn)` -> (cl t1..tn) via the `or` rule, using
                // the disjuncts in TERM order (Carcara's `or` is order-sensitive).
                std::string stepId =
                    proof.step(a.clauseTerms, "or", {hId});
                idToStep[s.id] = stepId;
            }
        } else {
            // Derived clause: resolve its antecedent chain. Resolution is
            // order-insensitive, so the LRAT lit order is fine here.
            std::vector<std::string> premises;
            premises.reserve(s.chain.size());
            for (int64_t c : s.chain) {
                auto it = idToStep.find(c);
                if (it == idToStep.end()) return std::nullopt;  // dangling hint
                premises.push_back(it->second);
            }
            std::vector<std::string> clause;
            clause.reserve(s.lits.size());
            for (int lit : s.lits) {
                auto t = renderLit(lit, varTerm);
                if (!t) return std::nullopt;
                clause.push_back(*t);
            }
            std::string stepId = proof.step(clause, "resolution", premises);
            idToStep[s.id] = stepId;
            if (clause.empty()) sawEmpty = true;
        }
    }

    // 3. A genuine refutation ends in the empty clause.
    if (!sawEmpty) return std::nullopt;
    return proof;
}

#endif  // XOLVER_ENABLE_PROOFS

} // namespace proof
} // namespace xolver
