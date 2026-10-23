#include "quantifiers/real/Solver.h"
#include "quantifiers/real/Problem.h"
#include <algorithm>
#include <unordered_map>

namespace xolver::quantifiers::real {
SolverAnswer solve(const Roots& roots, Limits limits) {
    try {
        Resources resources(limits);
        auto problem = compile(roots, resources);
        auto kernel = createPolynomialKernel();
        // Kernel variable order follows the quantifier prefix. Native traversal
        // can encounter a free symbol inside a binder; it must still be outside
        // every bound quantifier in satisfiability and in algebraic lifting.
        std::unordered_map<VarId, VarId> rename;
        for (auto& binder : problem.prefix) {
            const auto v = kernel->getOrCreateVar("q" + std::to_string(rename.size()));
            if (!rename.emplace(binder.variable, v).second)
                throw std::logic_error("duplicate variable in real prenex prefix");
            binder.variable = v;
        }
        for (auto& atom : problem.atoms) {
            RationalPolynomial polynomial;
            for (const auto& [powers, coefficient] : atom.polynomial.terms()) {
                auto mapped = powers;
                for (auto& [v, degree] : mapped) v = rename.at(v);
                std::sort(mapped.begin(), mapped.end());
                polynomial.addTerm(mapped, coefficient);
            }
            polynomial.normalize();
            atom.polynomial = std::move(polynomial);
        }
        for (auto& v : problem.free) v.variable = rename.at(v.variable);
        return decompose(problem, *kernel, resources);
    } catch (const Exhausted& error) {
        SolverAnswer answer; answer.reason = error.what(); return answer;
    } catch (const Unsupported& error) {
        SolverAnswer answer; answer.reason = error.what(); return answer;
    } catch (const std::invalid_argument& error) {
        SolverAnswer answer; answer.reason = std::string("invalid real arithmetic input: ") + error.what(); return answer;
    } catch (const std::bad_alloc&) {
        SolverAnswer answer; answer.reason = "quantifier memory exhausted"; return answer;
    }
}
}
