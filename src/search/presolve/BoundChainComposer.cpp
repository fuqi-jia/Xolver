#include "base/RuntimeConfig.h"
#include "search/presolve/BoundChainComposer.h"
#include "base/EnvParam.h"

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>

namespace xolver {
namespace {

mpq_class linearCoeff(const RationalPolynomial& p, VarId v) {
    MonomialKey key = {{v, 1}};
    auto it = p.terms().find(key);
    return it == p.terms().end() ? mpq_class(0) : it->second;
}

ReasonNode unionReasons(const PresolveState& st, const ReasonNode& a, const ReasonNode& b) {
    ReasonNode out;
    std::vector<SatLit> lits = st.ledger.flattenReasons(a);
    auto bl = st.ledger.flattenReasons(b);
    lits.insert(lits.end(), bl.begin(), bl.end());
    std::sort(lits.begin(), lits.end(), [](SatLit x, SatLit y) {
        return x.var != y.var ? x.var < y.var : x.sign < y.sign;
    });
    lits.erase(std::unique(lits.begin(), lits.end()), lits.end());
    out.baseLiterals = std::move(lits);
    return out;
}

} // namespace

bool BoundChainComposer::run(PresolveState& st) {
    bool made = false;
    const size_t origN = st.atoms.size();
    const size_t kMaxAtoms = static_cast<size_t>(std::max(1,
        config::read<config::ReadKind::Int>("XOLVER_NRA_BOUNDCHAIN_MAX_ATOMS", 2000)));
    const long kMaxWork = static_cast<long>(std::max(1,
        config::read<config::ReadKind::Int>("XOLVER_NRA_BOUNDCHAIN_MAX_WORK", 1500000)));
    const bool diag = config::read<config::ReadKind::Presence>("XOLVER_PRESOLVE_DIAG");
    if (origN > kMaxAtoms) {
        if (diag) std::cerr << "[BOUNDCHAIN] skip: origN=" << origN
                            << " > cap=" << kMaxAtoms << '\n';
        return false;
    }

    struct Coefficient { VarId variable; mpq_class value; };
    struct Source {
        size_t atom;
        Relation relation;
        std::vector<Coefficient> coefficients;
    };
    std::vector<Source> sources;
    sources.reserve(origN);
    using Position = std::pair<size_t, size_t>;
    std::map<VarId, std::vector<Position>> positive;
    for (size_t index = 0; index < origN; ++index) {
        const auto& atom = st.atoms[index];
        if (!atom.live || (atom.rel != Relation::Lt && atom.rel != Relation::Leq)) continue;
        Source source{index, atom.rel, {}};
        for (const auto variable : atom.poly.variables()) {
            if (atom.poly.degree(variable) != 1) continue;
            auto coefficient = linearCoeff(atom.poly, variable);
            if (coefficient != 0) source.coefficients.push_back({variable, std::move(coefficient)});
        }
        if (source.coefficients.empty()) continue;
        const auto sourceIndex = sources.size();
        for (size_t i = 0; i < source.coefficients.size(); ++i) {
            const auto& coefficient = source.coefficients[i];
            if (coefficient.value > 0) positive[coefficient.variable].push_back({sourceIndex, i});
        }
        sources.push_back(std::move(source));
    }
    if (positive.empty()) return false;

    // A relation and its exact canonical terms identify a fact. Premises stay
    // with the first live occurrence; no sign or strictness is discarded.
    using Terms = FlatMonomialMap<mpq_class>::Storage;
    using FactKey = std::pair<Relation, Terms>;
    std::set<FactKey> known;
    for (const auto& atom : st.atoms)
        if (atom.live) known.emplace(atom.rel, Terms(atom.poly.terms().begin(), atom.poly.terms().end()));
    auto newFact = [&](Relation relation, const RationalPolynomial& poly) {
        return known.emplace(relation, Terms(poly.terms().begin(), poly.terms().end())).second;
    };

    long work = 0;
    for (size_t ai = 0; ai < sources.size(); ++ai) {
        const auto& a = sources[ai];
        // Join only opposite-sign linear occurrences. Ordering by the original
        // second source and then variable retains the former derivation order.
        std::map<size_t, std::vector<Position>> partners;
        for (size_t i = 0; i < a.coefficients.size(); ++i) {
            const auto& coefficient = a.coefficients[i];
            if (coefficient.value >= 0) continue;
            const auto matches = positive.find(coefficient.variable);
            if (matches == positive.end()) continue;
            for (const auto& [bi, j] : matches->second)
                if (bi != ai) partners[bi].push_back({i, j});
        }
        if (partners.empty()) continue;
        // New atoms can reallocate st.atoms. Retain the first source locally
        // and access other original sources by stable index only when needed.
        const auto polyA = st.atoms[a.atom].poly;
        const auto reasonsA = st.atoms[a.atom].reasons;
        for (const auto& [bi, variables] : partners) {
            const auto& b = sources[bi];
            for (const auto& [i, j] : variables) {
                if (work > kMaxWork) {
                    if (diag) std::cerr << "[BOUNDCHAIN] work budget hit: origN=" << origN
                                        << " work=" << work << " made=" << made << '\n';
                    return made;
                }
                ++work;
                const auto variable = a.coefficients[i].variable;
                const auto& cA = a.coefficients[i].value;
                const auto& cB = b.coefficients[j].value;
                RationalPolynomial pa = polyA;
                pa *= mpq_class(1) / abs(cA);
                RationalPolynomial pb = st.atoms[b.atom].poly;
                pb *= mpq_class(1) / abs(cB);
                RationalPolynomial combo = pa + pb;
                combo.normalize();
                if (combo.contains(variable) || combo.variables().size() > 1) continue;

                const Relation relation = a.relation == Relation::Lt || b.relation == Relation::Lt
                    ? Relation::Lt : Relation::Leq;
                auto reasons = unionReasons(st, reasonsA, st.atoms[b.atom].reasons);
                if (combo.isConstant()) {
                    if (!relationHoldsForConstant(combo.constantValue(), relation)) {
                        st.hasConflict = true;
                        st.conflict.clause = std::move(reasons.baseLiterals);
                        return true;
                    }
                    if (combo.isZero() && relation == Relation::Leq) {
                        pb.normalize();
                        ++work;
                        if (!pb.isZero() && newFact(Relation::Eq, pb)) {
                            st.atoms.push_back({std::move(pb), Relation::Eq, std::move(reasons), true});
                            made = true;
                        }
                    }
                    continue;
                }
                ++work;
                if (!newFact(relation, combo)) continue;
                st.atoms.push_back({std::move(combo), relation, std::move(reasons), true});
                made = true;
            }
        }
    }
    return made;
}

} // namespace xolver
