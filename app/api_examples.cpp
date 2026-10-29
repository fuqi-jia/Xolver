#include "applications/maxsmt/Solver.h"
#include "applications/smt/Solver.h"
#include "ir/NativeBuilder.h"
#include "parallel/ThreadPool.h"
#include <iostream>

int main() {
    using namespace xolver;
    parallel::ThreadPool executor(2);
    auto first = executor.submit([](int x) { return x * 2; }, 21);
    auto second = executor.submit([] { return std::string("ready"); });
    std::cout << "parallel: " << first.get() << ", " << second.get() << '\n';

    native::Nodes nodes({});
    auto boolean = SOMTParser::SortManager::getBool();
    auto a = nodes.make(boolean, native::K::NT_VAR, {}, "a");
    auto b = nodes.make(boolean, native::K::NT_VAR, {}, "b");
    applications::maxsmt::Problem problem;
    problem.hard = {nodes.negate(nodes.all({a, b}))};
    problem.soft = {{a, mpq_class(3, 2), "prefer-a"}, {b, 1, "prefer-b"}};
    applications::maxsmt::Solver maxsmt([](const NativeAssertions& query) {
        return applications::smt::Solver().solve({query, {}, {}, {}});
    });
    const auto answer = maxsmt.solve(problem);
    if (answer.status != applications::maxsmt::Status::Optimal || !answer.cost) {
        std::cerr << "maxsmt: " << answer.reason << '\n';
        return 1;
    }
    std::cout << "maxsmt: optimal cost=" << answer.cost->get_str()
              << ", violated=" << problem.soft.at(answer.violatedSoft.at(0)).label << '\n';
}
