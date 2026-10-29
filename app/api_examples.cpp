#include "applications/satisfiability/sat/Solver.h"
#include "applications/optimization/maxsat/Solver.h"
#include "applications/optimization/maxsmt/Solver.h"
#include "applications/satisfiability/smt/Solver.h"
#include "ir/NativeBuilder.h"
#include "parallel/ThreadPool.h"
#include <iostream>

int main() {
    using namespace xolver;
    parallel::ThreadPool executor(2);
    auto first = executor.submit([](int x) { return x * 2; }, 21);
    auto second = executor.submit([] { return std::string("ready"); });
    std::cout << "parallel: " << first.get() << ", " << second.get() << '\n';

    applications::satisfiability::sat::Problem satProblem;
    satProblem.clauses = {{1, 2}, {-1}};
    const auto sat = applications::satisfiability::sat::Solver().solve(satProblem);
    if (sat.status != applications::satisfiability::sat::Status::Sat) return 1;
    std::cout << "sat: satisfiable\n";
    applications::optimization::maxsat::Problem maxsatProblem;
    maxsatProblem.hard = {{-1, -2}};
    maxsatProblem.soft = {{{1}, 2, "a"}, {{2}, 1, "b"}};
    applications::optimization::maxsat::Solver maxsat([](const NativeAssertions& roots) {
        return applications::satisfiability::smt::Solver().solve({roots, {}, {}, {}});
    });
    const auto maxsatAnswer = maxsat.solve(maxsatProblem);
    if (maxsatAnswer.status != applications::optimization::maxsat::Status::Optimal ||
        !maxsatAnswer.cost || *maxsatAnswer.cost != 1) return 1;
    std::cout << "maxsat: optimal cost=1\n";

    native::Nodes nodes({});
    auto boolean = SOMTParser::SortManager::getBool();
    auto a = nodes.make(boolean, native::K::NT_VAR, {}, "a");
    auto b = nodes.make(boolean, native::K::NT_VAR, {}, "b");
    applications::optimization::maxsmt::Problem problem;
    problem.hard = {nodes.negate(nodes.all({a, b}))};
    problem.soft = {{a, mpq_class(3, 2), "prefer-a"}, {b, 1, "prefer-b"}};
    applications::optimization::maxsmt::Solver maxsmt([](const NativeAssertions& query) {
        return applications::satisfiability::smt::Solver().solve({query, {}, {}, {}});
    });
    const auto answer = maxsmt.solve(problem);
    if (answer.status != applications::optimization::maxsmt::Status::Optimal || !answer.cost) {
        std::cerr << "maxsmt: " << answer.reason << '\n';
        return 1;
    }
    std::cout << "maxsmt: optimal cost=" << answer.cost->get_str()
              << ", violated=" << problem.soft.at(answer.violatedSoft.at(0)).label << '\n';
}
