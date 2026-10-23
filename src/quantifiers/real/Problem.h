#pragma once
#include "algebra/poly/RationalPolynomial.h"
#include "quantifiers/FiniteFormula.h"
#include <string>
#include <vector>

namespace xolver::quantifiers::real {
struct Binder { VarId variable; bool universal; };
struct Atom { RationalPolynomial polynomial; Relation relation; };
struct Connective {
    enum class Kind { False, True, Atom, And, Or } kind;
    std::size_t atom = 0;
    std::vector<std::size_t> children;
};
struct FreeVariable { VarId variable; std::string name; bool boolean; };
// Prenex real polynomial formula. Boolean variables use the exact domain {0,1}.
struct Problem {
    std::vector<Binder> prefix;
    std::vector<Atom> atoms;
    std::vector<Connective> matrix;
    std::size_t root = 0;
    std::vector<FreeVariable> free;
};
Problem compile(const Roots&, Resources&);
SolverAnswer decompose(const Problem&, PolynomialKernel&, Resources&);
}
