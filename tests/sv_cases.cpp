#include "applications/smt/Solver.h"
#include "applications/sv/sl/Entailment.h"
#include "applications/sv/verification/ModelChecking.h"
#include "ir/NativeSubstitution.h"
#include <filesystem>
#include <fstream>
#include <nlohmann/json.hpp>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace v = applications::sv::verification;
namespace {
void require(bool condition, const char *message) {
    if (!condition)
        throw std::runtime_error(message);
}
void write(const std::filesystem::path &path, const std::string &text) {
    std::ofstream stream;
    stream.exceptions(std::ios::failbit | std::ios::badbit);
    stream.open(path);
    stream << text;
}
struct Export {
    std::filesystem::path output;
    nlohmann::json cases = nlohmann::json::array();
    void query(const NativeAssertions &assertions, Result result, const std::string &group,
               bool heap = false) {
        require(result != Result::Unknown, "evidence query is unknown");
        std::set<native::Node> visited;
        std::map<std::string, native::Node> variables;
        auto pending = assertions;
        while (!pending.empty()) {
            auto n = pending.back();
            pending.pop_back();
            if (!visited.insert(n).second)
                continue;
            require(bool(n), "null evidence node");
            auto k = n->getKind();
            require(k != native::K::NT_UF_APPLY && k != native::K::NT_FUNC_REC &&
                        k != native::K::NT_FUNC_PARAM,
                    "evidence exporter needs an explicit function declaration");
            if (k == native::K::NT_VAR) {
                auto [it, inserted] = variables.emplace(n->getName(), n);
                require(inserted || it->second == n, "ambiguous evidence symbol");
            }
            for (auto child : SOMTParser::children(n))
                pending.push_back(child);
        }
        std::string text = "(set-logic ALL)\n";
        if (heap)
            text += "(declare-heap (Int Int))\n";
        for (const auto &[name, n] : variables)
            text += "(declare-const " + SOMTParser::dumpSMTLIB2(n) + " " +
                    n->getSort()->toString() + ")\n";
        for (auto n : assertions)
            text += "(assert " + SOMTParser::dumpSMTLIB2(n) + ")\n";
        text += "(check-sat)\n";
        auto file = std::to_string(cases.size()) + ".smt2";
        write(output / file, text);
        cases.push_back({{"input", file},
                         {"group", group},
                         {"heap", heap},
                         {"expected", result == Result::Sat ? "sat" : "unsat"}});
    }
};
DecisionOracle decide = [](const NativeAssertions &q) {
    return applications::smt::Solver().solve({q, {}, {}, {}});
};
void safety(Export &out) {
    native::Nodes b({});
    auto integer = SOMTParser::SortManager::getInt();
    auto x = b.make(integer, native::K::NT_VAR, {}, "x");
    auto xp = b.make(integer, native::K::NT_VAR, {}, "xp");
    auto num = [&](int value) {
        return b.make(integer, native::K::NT_CONST, {}, std::to_string(value));
    };
    v::TransitionSystem s;
    s.state = {{x, xp}};
    s.initial = {b.equal(x, num(0))};
    s.transition = {b.equal(xp, b.make(integer, native::K::NT_ADD, {x, num(1)}))};
    s.safety = b.logical(native::K::NT_GE, {x, num(0)});
    auto check = [&](const std::string &group, NativeAssertions candidates = {},
                     v::SafetyMethod method = v::SafetyMethod::Induction) {
        auto answer = v::SafetySolver(decide, {6}, method).solve({s, candidates});
        require(answer.status == v::SafetyStatus::Safe, "expected safety proof");
        require(bool(answer.certificate), "missing safety certificate");
        DecisionOracle recording = [&](const NativeAssertions &query) {
            auto result = decide(query);
            out.query(query, result.result, group);
            return result;
        };
        require(v::CertificateSolver(recording).solve({s, *answer.certificate}).status ==
                    v::Status::Valid,
                "safety certificate rejected");
    };
    check("integer-induction");
    check("candidate-invariant", {s.safety, b.equal(x, num(0))});
    auto y = b.make(integer, native::K::NT_VAR, {}, "y");
    auto yp = b.make(integer, native::K::NT_VAR, {}, "yp");
    auto copy = s;
    s.state.push_back({y, yp});
    s.initial.push_back(b.equal(y, num(0)));
    s.transition = {b.equal(xp, y), b.equal(yp, b.make(integer, native::K::NT_ADD, {y, num(1)}))};
    check("dependent-invariants", {b.equal(x, num(0)), b.equal(y, num(0)), s.safety,
                                   b.logical(native::K::NT_GE, {y, num(0)})});
    s = copy;
    NativeAssertions edges;
    for (auto [a, c] :
         std::vector<std::pair<int, int>>{{0, 1}, {1, 2}, {2, 3}, {3, 3}, {4, 5}, {5, 5}})
        edges.push_back(b.all({b.equal(x, num(a)), b.equal(xp, num(c))}));
    s.transition = {b.any(edges)};
    s.safety = b.negate(b.equal(x, num(5)));
    check("two-step-induction");
    check("reachability-completion", {}, v::SafetyMethod::Bounded);
    s = copy;
    auto input = b.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, "input");
    s.inputs = {input};
    s.transition = {b.any({b.all({b.equal(x, num(0)), b.negate(input), b.equal(xp, num(1))}),
                           b.all({b.equal(x, num(1)), input, b.equal(xp, num(2))})})};
    s.safety = b.logical(native::K::NT_LT, {x, num(2)});
    auto unsafe = v::SafetySolver(decide, {3}).solve({s, {}});
    require(unsafe.status == v::SafetyStatus::Unsafe && unsafe.counterexample,
            "expected fresh-input counterexample");
    out.query(unsafe.counterexample->query, Result::Sat, "reachable-counterexample");
}
void separation(Export &out) {
    const std::vector<std::pair<std::string, std::string>> examples{
        {"(or (and (= n 0) sep.emp) (and (> n 0) (sep (pto n (- n 1)) (p (- n 1)))))", "(>= n 0)"},
        {"(or (and (= n 0) sep.emp) (and (> n 0) (p (- n 1))))", "sep.emp"},
        {"(p n)", "false"}};
    for (const auto &[body, property] : examples) {
        SOMTParser::Parser parser;
        require(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(declare-const x Int)"
                                "(define-fun-rec p ((n Int)) Bool " +
                                body + ")(assert (p x))"),
                "cannot parse SL evidence");
        sl::EntailmentProblem problem;
        auto &context = problem.context;
        context.location = parser.getHeapLocationSort();
        context.data = parser.getHeapDataSort();
        context.assertions = parser.getAssertions();
        context.declarations = parser.getDeclaredVariables();
        context.recursion = sl::RecursiveSemantics::LeastFixedPoint;
        for (const auto &d : parser.getRecursiveDefinitions())
            context.definitions.push_back(
                {d.symbol, d.definition->getFuncBody(), d.definition->getFuncParams()});
        native::Nodes b(context.assertions);
        auto externalProperty = property;
        if (property == "(>= n 0)")
            externalProperty = "(>= x 0)";
        problem.conclusion = parser.mkExpr(externalProperty);
        std::map<native::Node, native::Node> replacement{
            {parser.mkExpr("x"), context.definitions[0].parameters[0]}};
        std::map<native::Node, native::Node> memo;
        context.invariantCandidates = {
            {context.definitions[0].symbol,
             native::substitute(problem.conclusion, replacement, memo, b)}};
        auto answer = sl::EntailmentSolver({3000000, 256}).solve(problem);
        require(answer.status == sl::EntailmentStatus::Valid && answer.certificate,
                "expected recursive SL entailment proof");
        require(!answer.inference.obligations.empty(), "no retained SL induction obligations");
        for (const auto &query : answer.inference.obligations)
            out.query(query, Result::Unsat, "sl-induction", true);
        require(sl::EntailmentCertificateSolver({3000000, 256})
                        .solve({problem, *answer.certificate})
                        .status == sl::EntailmentStatus::Valid,
                "SL certificate rejected");
    }
}
} // namespace
int main(int argc, char **argv) {
    if (argc != 2)
        return 2;
    Export out{argv[1]};
    if (!std::filesystem::create_directory(out.output))
        return 3;
    safety(out);
    separation(out);
    write(out.output / "cases.json", out.cases.dump(2) + "\n");
}
