#include "applications/smt/Solver.h"
#include "applications/sv/verification/Range.h"
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
    namespace v = applications::sv::verification;
    nlohmann::json output;
    try {
        if (argc != 2)
            throw std::invalid_argument("usage: xolver-sv obligation.smt2");
        std::ifstream stream(argv[1]);
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
        v::Obligation obligation{argv[1], assertions, conclusion};
        obligation.assumptions.pop_back();
        DecisionOracle oracle = [](const NativeAssertions &q) {
            return applications::smt::Solver().solve({q, {}, {}, {}});
        };
        auto answer = v::RangeAssistedSolver(oracle).solve(obligation);
        const char *status = answer.status == v::Status::Valid     ? "valid"
                             : answer.status == v::Status::Invalid ? "invalid"
                                                                   : "unknown";
        output = {{"status", status},
                  {"method", answer.method == v::VerificationMethod::Interval ? "interval" : "smt"},
                  {"reason", answer.reason},
                  {"work", answer.intervalWork},
                  {"certificate_replayed", bool(answer.certificate)}};
        output["program_verified"] = false;
        std::cout << output.dump() << '\n';
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 2;
    }
}
