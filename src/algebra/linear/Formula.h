#pragma once
#include "algebra/linear/LinearExpr.h"
#include "base/WorkBudget.h"
#include <map>

namespace xolver::linear {
struct UnsupportedFormula : std::runtime_error {
    using std::runtime_error::runtime_error;
};
struct Variable {
    std::string name;
    bool integer = false, boolean = false;
};
struct Affine {
    std::vector<mpq_class> coefficients;
    mpq_class constant = 0;
};
struct Inequality {
    Affine expression;
    bool strict = false;
}; // expression <= 0, or < 0
using Conjunction = std::vector<Inequality>;
using Disjunction = std::vector<Conjunction>;
// NativeTerms only indexes the original parser DAG; no second expression graph.
class Formula {
    const NativeTerms &terms_;
    WorkBudget &budget_;
    std::map<std::string, std::size_t> indices_;
    std::size_t depth_ = 0;
    Disjunction boolean(ExprId, bool negative);
    Disjunction combine(Disjunction, const Disjunction &, bool conjunction);
    Disjunction atom(Affine, Kind, bool negative);

  public:
    std::vector<Variable> variables;
    Formula(const NativeTerms &, const std::vector<ExprId> &roots, WorkBudget &);
    Affine affine(ExprId) const;
    Disjunction compile(const std::vector<ExprId> &);
};
} // namespace xolver::linear
