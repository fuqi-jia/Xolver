#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/DynamicAtomRegistrar.h"
#include "theory/core/TheoryPropagatorCallbacks.h"
#include <unordered_map>
#include <unordered_set>

namespace xolver {

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

    // Force a theory atom's SAT literal to a constant truth value via a unit
    // clause. Used for arithmetic atoms that the polynomial converter proves are
    // always-true (Tautology) or always-false (Conflict) — e.g. `0 != 0` after
    // constant propagation. Without this the literal is left free and SAT may
    // satisfy a provably-false atom vacuously (false-SAT).
    void pinLiteral(SatVar satVar, bool value);

    // Bool-variable → SatVar lookup, populated by the Atomizer for every
    // Bool Variable it processes (formula-position pure Bool vars, e.g.
    // boolpur_K Tseitin proxies). Lets a theory solver locate the SAT
    // literal corresponding to a known Bool var by NAME and pin it from
    // a theory stage (e.g. NIA Farkas-Or committing the chosen Or
    // branch's proxy literal so SAT-CDCL converges on the matching
    // assignment instead of exploring competing branches).
    void registerBoolVariable(const std::string& name, SatVar satVar);
    std::optional<SatVar> findBoolVariableSatVar(const std::string& name) const;

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

    // iter-50: lookup SAT var by ExprId regardless of payload kind.
    // Returns nullopt if no registered atom matches.
    std::optional<SatVar> findSatVarByExprId(ExprId expr) const;

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
    // Bool Variable name → SatVar (Atomizer-populated).
    std::unordered_map<std::string, SatVar> boolVarSatVars_;
    // EUF equality dedup keyed by canonical (min,max) ExprId pair.
    std::unordered_map<uint64_t, size_t> eufEqLookup_;

    ExprId nextSyntheticExprId_ = static_cast<ExprId>(0x80000000);
    bool unsupportedTheorySeen_ = false;

    void observeIfNeeded(SatVar v);
};

} // namespace xolver
