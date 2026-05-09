#pragma once

#include "theory/TheorySolver.h"
#include "GeneralSimplex.h"
#include <gmpxx.h>
#include <unordered_map>
#include <vector>
#include <string>

namespace nlcolver {

/**
 * LRA theory solver wrapper around GeneralSimplex.
 *
 * Responsibilities:
 *   - Extract linear constraints from CoreExpr
 *   - Map variables/constraints to GeneralSimplex indices
 *   - Handle disequality (Neq) via guarded split lemmas
 *   - Translate GeneralSimplex conflicts to TheoryConflict clauses
 */
class SimplexSolver : public TheorySolver {
public:
    SimplexSolver();

    TheoryId id() const override { return TheoryId::LRA; }

    void push() override;
    void pop(uint32_t n) override;
    void assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) override;
    TheoryCheckResult check(const CoreIr& ir) override;
    void reset() override;

private:
    GeneralSimplex gs_;

    // Variable name -> GeneralSimplex var index
    std::unordered_map<std::string, int> varToIndex_;

    // Canonical linear form key for constraint deduplication
    struct LinearForm {
        std::vector<std::pair<std::string, mpq_class>> terms;  // sorted by var name
        mpq_class rhs;
        bool operator==(const LinearForm& o) const;
    };

    struct LinearFormHash {
        std::size_t operator()(const LinearForm& f) const;
    };

    std::unordered_map<LinearForm, int, LinearFormHash> formToAux_;

    struct AtomInfo {
        int auxVar;
        Relation rel;
    };
    std::unordered_map<ExprId, AtomInfo> exprToAtom_;

    // Disequalities that need split lemmas
    struct DiseqInfo {
        int auxVar;
        SatLit lit;
    };
    std::vector<DiseqInfo> disequalities_;

    // Reason tracking for conflict translation: auxVar -> (lowerReason, upperReason)
    std::unordered_map<int, std::pair<std::optional<SatLit>, std::optional<SatLit>>> boundReasons_;

    // Helpers
    int getOrCreateVar(const std::string& name);
    bool extractLinearConstraint(ExprId eid, const CoreIr& ir,
                                  std::unordered_map<std::string, mpq_class>& coeffs,
                                  mpq_class& rhs, Relation& rel);
    bool registerAtom(const TheoryAtom& atom, const CoreIr& ir);
    void assertBound(int auxVar, Relation rel, bool value, SatLit reasonLit);
    TheoryCheckResult handleDisequalities();
    TheoryConflict translateConflict();
    TheoryLemma buildDiseqSplitLemma(const DiseqInfo& d);
};

} // namespace nlcolver
