#pragma once

#ifdef NLCOLVER_HAS_CADICAL

#include <cadical.hpp>
#include "theory/TheoryAtomRegistry.h"
#include "theory/TheoryManager.h"
#include "theory/TheoryLemmaDatabase.h"

namespace nlcolver {

class CadicalBackend;

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

    void setPendingClause(const std::vector<SatLit>& lits);
    void setPendingClause(const TheoryLemma& lemma);
    void terminateSolve();
};

} // namespace nlcolver

#endif // NLCOLVER_HAS_CADICAL
