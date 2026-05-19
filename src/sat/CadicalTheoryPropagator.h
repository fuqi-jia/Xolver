#pragma once

#ifdef NLCOLVER_HAS_CADICAL

#include <cadical.hpp>
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryManager.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAssignmentView.h"

namespace nlcolver {

class CadicalBackend;

/**
 * Lightweight assignment view populated from CaDiCaL's cb_check_found_model model.
 * Safe to query from TheoryManager::check() because it does not call back into CaDiCaL.
 */
class CadicalAssignmentView : public TheoryAssignmentView {
public:
    void clear() { values_.clear(); }
    void setVarValue(SatVar var, bool value) {
        if (var >= values_.size()) values_.resize(var + 1, 0);
        values_[var] = value ? 1 : -1;
    }
    LitValue value(SatLit lit) const override {
        if (lit.var >= values_.size()) return LitValue::Unknown;
        int v = values_[lit.var];
        if (v == 0) return LitValue::Unknown;
        bool varTrue = (v > 0);
        bool litTrue = lit.sign ? varTrue : !varTrue;
        return litTrue ? LitValue::True : LitValue::False;
    }
private:
    std::vector<int8_t> values_;
};

/**
 * CadicalTheoryPropagator: bridges CaDiCaL's ExternalPropagator to our theory stack.
 */
class CadicalTheoryPropagator : public CaDiCaL::ExternalPropagator {
public:
    CadicalTheoryPropagator(
        TheoryAtomRegistry& registry,
        TheoryManager& tm,
        TheoryLemmaDatabase& lemmaDb,
        CadicalBackend& backend
    );

    // --- IPASIR-UP callbacks ---
    void notify_assignment(const std::vector<int>& lits) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;

    bool cb_check_found_model(const std::vector<int>& model) override;

    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;

private:
    TheoryAtomRegistry& registry_;
    TheoryManager& tm_;
    TheoryLemmaDatabase& lemmaDb_;
    CadicalBackend& backend_;

    int currentLevel_ = 0;
    std::vector<SatLit> pendingClause_;
    size_t pendingClausePos_ = 0;
    bool hasPendingClause_ = false;
    bool abortWithUnknown_ = false;
    int modelCheckCount_ = 0;
    static constexpr int MAX_MODEL_CHECKS = 10000;
    CadicalAssignmentView assignmentView_;
    std::unordered_map<SatVar, int> varToLevel_;

    CadicalAssignmentView& assignmentView() { return assignmentView_; }

    void setPendingClause(const std::vector<SatLit>& lits);
    void setPendingClause(const TheoryLemma& lemma);
    void terminateSolve();
    bool isClauseFalsifiedByCurrentModel(const std::vector<SatLit>& clause) const;
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
