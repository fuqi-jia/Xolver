#include "applications/satisfiability/asp/Solver.h"
#include <nlohmann/json.hpp>
#include <charconv>
#include <fstream>
#include <iostream>
#include <stdexcept>

namespace {
using namespace xolver::applications::satisfiability::asp;
using Json = nlohmann::json;
const char* statusName(Status status) {
    switch (status) {
        case Status::Sat: return "sat";
        case Status::Optimal: return "optimal";
        case Status::Unsat: return "unsat";
        case Status::Unknown: return "unknown";
        case Status::InvalidInput: return "invalid_input";
        case Status::Unsupported: return "unsupported";
    }
    return "unknown";
}
void costs(const Answer& answer) {
    std::cout << '[';
    for (std::size_t i = 0; i < answer.costs.size(); ++i) {
        if (i) std::cout << ',';
        std::cout << answer.costs[i].get_str(); // Exact JSON integers, without a double conversion.
    }
    std::cout << ']';
}
void print(const Answer& answer) {
    const std::string result = answer.status == Status::Unsat ? "UNSATISFIABLE"
        : answer.status == Status::Optimal ? "OPTIMUM FOUND"
        : answer.status == Status::Sat ? "SATISFIABLE" : "UNKNOWN";
    Json metadata{{"status", statusName(answer.status)}, {"reason", answer.reason},
        {"stable_model_checked", answer.model.has_value()}, {"sat_calls", answer.satCalls},
        {"unfounded_cuts", answer.unfoundedCuts}, {"proved_levels", answer.provedLevels},
        {"priorities", answer.priorities}, {"atom_ids", answer.atomIds}};
    metadata["true_atoms"] = answer.model ? Json(*answer.model) : Json(nullptr);
    std::cout << "{\"Solver\":\"Xolver ASP\",\"Result\":" << Json(result).dump()
              << ",\"Call\":[{\"Witnesses\":[";
    if (answer.model) {
        std::cout << "{\"Value\":" << Json(answer.shown).dump();
        if (!answer.costs.empty()) { std::cout << ",\"Costs\":"; costs(answer); }
        std::cout << '}';
    }
    std::cout << "]}],\"Models\":{\"Number\":" << (answer.model ? 1 : 0)
              << ",\"More\":" << Json(answer.status == Status::Sat ? "yes" : "no").dump();
    if (!answer.costs.empty()) { std::cout << ",\"Costs\":"; costs(answer); }
    std::cout << "},\"Xolver\":" << metadata.dump() << "}\n";
    std::cout.flush();
}
}

int main(int argc, char** argv) {
    try {
        std::int64_t milliseconds = 60000;
        std::string path;
        bool optimize = true;
        for (int i = 1; i < argc; ++i) {
            const std::string option = argv[i];
            if (option == "--timeout-ms") {
                if (++i == argc) throw std::invalid_argument("missing --timeout-ms value");
                const std::string value = argv[i];
                const auto parsed = std::from_chars(value.data(), value.data()+value.size(), milliseconds);
                if (parsed.ec != std::errc{} || parsed.ptr != value.data()+value.size() || milliseconds < 0 ||
                    milliseconds > 86400000)
                    throw std::invalid_argument("timeout must be an integer in [0,86400000] milliseconds");
            } else if (option == "--opt-mode=ignore") optimize = false;
            else if (option == "--help") {
                std::cout << "Usage: xolver-asp [--timeout-ms N] [--opt-mode=ignore] [input.aspif]\n"
                             "Reads single-step ASPIF 1.0 and emits a Clingo-style JSON result.\n"
                             "N=0 removes the local deadline; source ASP requires a separate grounder.\n";
                return 0;
            } else if (!option.empty() && option.front() == '-')
                throw std::invalid_argument("unrecognized option " + option);
            else if (!path.empty()) throw std::invalid_argument("only one ASPIF input is accepted");
            else path = option;
        }
        const auto start = std::chrono::steady_clock::now();
        std::ifstream file;
        if (!path.empty()) {
            file.open(path, std::ios::binary);
            if (!file) throw std::invalid_argument("cannot open ASPIF input");
        }
        auto parsed = parseAspif(path.empty() ? std::cin : file);
        if (parsed.status != ParseResult::Status::Parsed) {
            Answer answer;
            answer.status = parsed.status == ParseResult::Status::Unsupported ? Status::Unsupported : Status::InvalidInput;
            answer.reason = parsed.reason;
            print(answer);
            return 0;
        }
        Problem problem{std::move(parsed.program), {}};
        problem.mode = optimize ? SolveMode::Optimize : SolveMode::Feasible;
        if (milliseconds) problem.limits.deadline = start + std::chrono::milliseconds(milliseconds);
        auto* protocol = std::cout.rdbuf();
        std::cout.rdbuf(std::cerr.rdbuf());
        const auto answer = Solver().solve(problem);
        std::cout.rdbuf(protocol);
        print(answer);
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 2;
    }
}
