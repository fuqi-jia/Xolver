#include "applications/satisfiability/smt/Solver.h"
#include "applications/verification/model_checking/Range.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include <fstream>
#include <iostream>
#include <nlohmann/json.hpp>
#include <somtparser/frontend/parser.h>

// A native client of the SV APIs. Input is an SMT-LIB obligation: preceding
// assertions are assumptions; the final assertion is the refutation condition.
// Negating that parsed condition also handles parser constant folding without
// relying on the final DAG node retaining a source-level NOT connective.
int main(int argc, char **argv) {
    using namespace xolver;
    namespace v = applications::verification::model_checking;
    nlohmann::json output;
    try {
        bool context = argc == 3 && std::string_view(argv[1]) == "context";
        if (argc != 2 && !context)
            throw std::invalid_argument("usage: xolver-sv [context] obligation.smt2");
        const char *path = argv[context ? 2 : 1];
        std::ifstream stream(path);
        if (!stream)
            throw std::invalid_argument("cannot open obligation");
        std::string source((std::istreambuf_iterator<char>(stream)), {});
        SOMTParser::Parser parser;
        preserveNativeTheories(*parser.getOptions());
        if (!parser.parseStr(source))
            throw std::invalid_argument("cannot parse obligation");
        auto assertions = parser.getAssertions();
        if (assertions.empty())
            throw std::invalid_argument("obligation requires a refutation assertion");
        auto conclusion = std::make_shared<SOMTParser::DAGNode>(
            SOMTParser::SortManager::getBool(), SOMTParser::NODE_KIND::NT_NOT, "not",
            std::vector<SOMTParser::Node>{assertions.back()});
        v::Obligation obligation{path, assertions, conclusion};
        obligation.assumptions.pop_back();
        DecisionOracle oracle = [](const NativeAssertions &q) {
            return applications::satisfiability::smt::Solver().solve({q, {}, {}, {}});
        };
        auto status = [](v::Status value) {
            return value == v::Status::Valid          ? "valid"
                   : value == v::Status::Invalid      ? "invalid"
                   : value == v::Status::InvalidInput ? "invalid-input"
                                                      : "unknown";
        };
        if (context) {
            auto answer = v::ContextSolver(oracle).solve(obligation);
            const char *feasibility = answer.context.result == Result::Sat     ? "sat"
                                      : answer.context.result == Result::Unsat ? "unsat"
                                                                               : "unknown";
            output = {{"status", status(answer.implication.status)},
                      {"context", feasibility},
                      {"context_reason", answer.context.reason},
                      {"reason", answer.implication.reason},
                      {"method", "smt"},
                      {"queries", answer.queries}};
        } else {
            auto answer = v::RangeAssistedSolver(oracle).solve(obligation);
            output = {{"status", status(answer.status)},
                      {"method", answer.method == v::VerificationMethod::Interval ? "interval" : "smt"},
                      {"reason", answer.reason},
                      {"work", answer.intervalWork},
                      {"certificate_replayed", bool(answer.certificate)}};
        }
        output["program_verified"] = false;
        std::cout << output.dump() << '\n';
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 2;
    }
}
