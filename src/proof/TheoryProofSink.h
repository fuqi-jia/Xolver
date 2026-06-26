#pragma once

#include "expr/types.h"
#include <string>
#include <utility>
#include <vector>

namespace xolver {
namespace proof {

// A theory conflict certificate collected during a proof-mode solve. The theory
// solver records the conflicting atoms by IR id (it has the SatLit->atom map but
// not necessarily the IR printer); the Solver, which owns the CoreIr, renders
// them to SMT-LIB at assembly. The data is only *trusted* insofar as the external
// checker (Carcara) accepts the assembled proof — a wrong certificate yields a
// rejected proof (caught offline), never a claimed-but-unsound one.
struct TheoryConflictCert {
    // The conflicting literals: (atom IR id, asserted-positively?). The tautology
    // clause negates each (double-negation simplified).
    std::vector<std::pair<ExprId, bool>> lits;
    std::string rule;                  // e.g. "la_generic"
    std::vector<std::string> args;     // rule args (Farkas multipliers; unit for
                                       // immediate LRA conflicts)
};

// Collector for theory certificates over one solve. Owned by the Solver; theory
// solvers reach the *active* instance via the thread-local accessor below (the
// solve is single-threaded — CLAUDE.md: a dedicated worker thread).
class TheoryProofSink {
public:
    void addConflict(TheoryConflictCert c) { conflicts_.push_back(std::move(c)); }
    const std::vector<TheoryConflictCert>& conflicts() const { return conflicts_; }
    void clear() { conflicts_.clear(); }
    bool empty() const { return conflicts_.empty(); }

private:
    std::vector<TheoryConflictCert> conflicts_;
};

// Thread-local active sink. Null unless a proof-mode solve installed one. Theory
// solvers push to it only when non-null; the no-proof path sees null and does
// nothing.
TheoryProofSink* activeProofSink();
void setActiveProofSink(TheoryProofSink* sink);

} // namespace proof
} // namespace xolver
