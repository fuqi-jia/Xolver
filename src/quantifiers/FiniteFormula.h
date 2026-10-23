#pragma once
#include "contracts/SolverAnswer.h"
#include "quantifiers/Resources.h"
#include "quantifiers/NativeInput.h"

namespace xolver::quantifiers {
// Native finite-domain compilation shares the Boolean connectives and binder
// scoping between QBF and QBV. Each binding receives independent Boolean bits.
SolverAnswer solveFinite(const Roots&, Limits, bool bitvectors);
namespace boolean { SolverAnswer solve(const Roots&, Limits = {}); }
namespace bitvector { SolverAnswer solve(const Roots&, Limits = {}); }
// Evaluate in a fixed interpretation. No free symbol is searched or reassigned.
// Unmentioned finite symbols use zero/false, matching model completion.
std::optional<std::string> finiteValue(const std::shared_ptr<SOMTParser::DAGNode>&,
                                     const TheoryModel&, Limits = {});
struct FiniteObjective {
    std::shared_ptr<SOMTParser::DAGNode> term;
    bool maximize = false;
    bool signedOrder = false;
};
struct FiniteAnalysis {
    SolverAnswer answer;
    std::optional<mpz_class> count;
    std::vector<mpz_class> objectives;
};
// Projection is explicit: an empty projection counts satisfiable formulas as
// one. Hidden free symbols are existentially abstracted. Objectives use exact
// lexicographic optimization over finite values; they do not count functions.
FiniteAnalysis analyzeFinite(const Roots&, const std::optional<Roots>& projection,
                             const std::vector<FiniteObjective>&, Limits = {});
}
