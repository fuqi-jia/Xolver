#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/DynamicAtomRegistrar.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <unordered_map>
#include <unordered_set>

namespace zolver {

class TheoryAtomRegistry : public TheoryAtomLookup {
public:
    TheoryAtomRegistry() = default;

    void setContext(SatSolver* sat, DynamicAtomRegistrar* registrar);

    void registerParsedTheoryAtom(
        SatVar satVar,
        ExprId exprId,
        TheoryId theory,
        const TheoryAtomPayload& payload
    );

    SatLit getOrCreateLinearBoundAtom(
        const LinearFormKey& lhs,
        Relation rel,
        const mpq_class& rhs,
        TheoryId theory
    );

    SatLit getOrCreatePolynomialAtom(
        PolyId poly,
        Relation rel,
        const mpq_class& rhs,
        TheoryId theory
    );

    bool findByExprId(ExprId expr, LinearFormKey& outLhs, Relation& outRel, mpq_class& outRhs) const;

    const TheoryAtomRecord* findBySatVar(SatVar v) const override;
    std::vector<SatVar> linearAtomVars() const override;
    const std::vector<TheoryAtomRecord>& records() const { return records_; }

    bool hasUnsupportedTheoryAtom() const { return unsupportedTheorySeen_; }
    void setUnsupportedTheorySeen() { unsupportedTheorySeen_ = true; }

    // Shared equality atom: Eq(a,b) for Nelson-Oppen combination.
    // Canonical key ensures Eq(a,b) and Eq(b,a) share one SatVar.
    SatLit getOrCreateSharedEqualityAtom(SharedTermId a, SharedTermId b);

    // Dynamic EUF equality atom Eq(lhs, rhs) over CoreIr ExprIds. Used by the
    // ArrayReasoner to emit Row2/Extensionality lemmas whose literals are NEW
    // equalities between array/select/index terms. Returns the positive
    // literal for (= lhs rhs); the negated literal denotes (distinct lhs rhs).
    // The created SAT var is observed so the propagator routes its assignment
    // back to the EUF solver as an EufAtomPayload before the clause is used.
    // Canonical key (min,max) ensures Eq(a,b) and Eq(b,a) share one SatVar.
    SatLit getOrCreateEufEqualityAtom(ExprId lhs, ExprId rhs);

private:
    SatSolver* sat_ = nullptr;
    DynamicAtomRegistrar* registrar_ = nullptr;

    std::vector<TheoryAtomRecord> records_;
    std::unordered_map<SatVar, size_t> satVarToIdx_;
    std::unordered_set<SatVar> observedVars_;

    struct LinearLookupKey {
        LinearFormKey form;
        Relation rel;
        mpq_class rhs;
        bool operator==(const LinearLookupKey& o) const {
            return form == o.form && rel == o.rel && rhs == o.rhs;
        }
    };
    struct LinearLookupKeyHash {
        std::size_t operator()(const LinearLookupKey& k) const {
            std::size_t h = LinearFormKeyHash{}(k.form);
            h ^= static_cast<std::size_t>(k.rel) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<std::string>{}(k.rhs.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<LinearLookupKey, size_t, LinearLookupKeyHash> linearLookup_;

    struct PolyLookupKey {
        PolyId poly;
        Relation rel;
        mpq_class rhs;
        bool operator==(const PolyLookupKey& o) const {
            return poly == o.poly && rel == o.rel && rhs == o.rhs;
        }
    };
    struct PolyLookupKeyHash {
        std::size_t operator()(const PolyLookupKey& k) const {
            std::size_t h = std::hash<PolyId>{}(k.poly);
            h ^= static_cast<std::size_t>(k.rel) + 0x9e3779b9 + (h << 6) + (h >> 2);
            h ^= std::hash<std::string>{}(k.rhs.get_str()) + 0x9e3779b9 + (h << 6) + (h >> 2);
            return h;
        }
    };
    std::unordered_map<PolyLookupKey, size_t, PolyLookupKeyHash> polyLookup_;
    std::unordered_map<uint64_t, size_t> sharedEqLookup_;
    // EUF equality dedup keyed by canonical (min,max) ExprId pair.
    std::unordered_map<uint64_t, size_t> eufEqLookup_;

    ExprId nextSyntheticExprId_ = static_cast<ExprId>(0x80000000);
    bool unsupportedTheorySeen_ = false;

    void observeIfNeeded(SatVar v);
};

} // namespace zolver
