#include "search/presolve/PolynomialEqualityCombination.h"
#include "base/WorkBudget.h"

#include <algorithm>
#include <map>
#include <set>
#include <vector>

namespace xolver {
namespace {

bool nonlinear(const MonomialKey& key) {
    // Canonical monomials contain positive exponents and no repeated variable.
    return key.size() > 1 || (!key.empty() && key.front().second > 1);
}

struct Row {
    RationalPolynomial polynomial;
    // Exact coefficients of original equalities. Zero coefficients are removed
    // so an equation that cancels out cannot weaken the final explanation.
    std::map<size_t, mpq_class> sources;
};

using Terms = FlatMonomialMap<mpq_class>::Storage;

Terms equalityKey(const RationalPolynomial& polynomial) {
    auto canonical = polynomial;
    if (!canonical.isZero() && canonical.terms().front().second < 0) canonical = -canonical;
    return {canonical.terms().begin(), canonical.terms().end()};
}

} // namespace

bool PolynomialEqualityCombination::run(PresolveState& st) {
    bool made = false;
    try {
        WorkBudget work(0);
        const auto tick = [&]() {
            work.tick();
            if (std::chrono::steady_clock::now() >= st.deadline)
                throw ResourceExhausted("polynomial equality combination allocation exhausted");
        };
        const size_t originalSize = st.atoms.size();
        std::map<MonomialKey, Row> basis;
        std::set<Terms> known;
        for (const auto& atom : st.atoms) {
            tick();
            if (atom.live && atom.rel == Relation::Eq && totalDegree(atom.poly) <= 1)
                known.insert(equalityKey(atom.poly));
        }
        for (size_t index = 0; index < originalSize; ++index) {
            tick();
            const auto& atom = st.atoms[index];
            if (!atom.live || atom.rel != Relation::Eq || totalDegree(atom.poly) <= 1)
                continue;
            // Affine inputs have zero nonlinear projection; their unit null
            // vectors only reproduce premises already present in the state.
            Row row{atom.poly, {{index, 1}}};
            bool independent = false;
            while (true) {
                tick();
                const auto pivot = std::find_if(row.polynomial.terms().begin(),
                    row.polynomial.terms().end(),
                    [](const auto& term) { return nonlinear(term.first); });
                if (pivot == row.polynomial.terms().end()) break;
                const mpq_class coefficient = pivot->second;
                const auto previous = basis.find(pivot->first);
                if (previous == basis.end()) {
                    const auto key = pivot->first;
                    row.polynomial *= mpq_class(1) / coefficient;
                    for (auto& [source, weight] : row.sources) {
                        tick();
                        (void)source;
                        weight /= coefficient;
                    }
                    basis.emplace(key, std::move(row));
                    independent = true;
                    break;
                }
                auto scaled = previous->second.polynomial;
                scaled *= coefficient;
                row.polynomial -= scaled;
                for (const auto& [source, weight] : previous->second.sources) {
                    tick();
                    auto [entry, inserted] = row.sources.try_emplace(source, 0);
                    (void)inserted;
                    entry->second -= coefficient * weight;
                    if (entry->second == 0) row.sources.erase(entry);
                }
            }
            if (independent || row.polynomial.isZero()) continue;

            // The nonlinear projection vanished. Publish only a complete,
            // exact linear combination; partial eliminations remain local.
            ReasonNode reasons;
            std::set<std::pair<SatVar, bool>> seen;
            for (const auto& [source, weight] : row.sources) {
                tick();
                (void)weight;
                for (const auto literal : st.ledger.flattenReasons(st.atoms[source].reasons))
                    if (seen.emplace(literal.var, literal.sign).second)
                        reasons.baseLiterals.push_back(literal);
            }
            if (row.polynomial.isConstant()) {
                st.hasConflict = true;
                st.conflict.clause = std::move(reasons.baseLiterals);
                return true;
            }
            if (!known.insert(equalityKey(row.polynomial)).second) continue;
            if (row.polynomial.terms().front().second < 0)
                row.polynomial = -row.polynomial;
            tick();
            st.atoms.push_back({std::move(row.polynomial), Relation::Eq, std::move(reasons)});
            made = true;
        }
    } catch (const ResourceExhausted&) {
        // Every published atom is complete and retains its original premises.
        // Discarding the local basis only loses optional further consequences.
    }
    return made;
}

} // namespace xolver
