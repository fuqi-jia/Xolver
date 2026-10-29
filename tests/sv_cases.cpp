#include "applications/satisfiability/smt/Solver.h"
#include "applications/verification/sl/Entailment.h"
#include "applications/verification/model_checking/Reachability.h"
#include "ir/NativeSubstitution.h"
#include <filesystem>
#include <fstream>
#include <nlohmann/json.hpp>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace v = applications::verification::model_checking;
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
        // Internal @ names are reserved by SMT-LIB. Rename free and bound
        // symbols simultaneously by identity, preserving scopes and sorts.
        native::Nodes b(assertions);
        std::map<native::Node, native::Node> renamed, memo;
        nlohmann::json symbols = nlohmann::json::object();
        for (const auto &[name, n] : variables) {
            auto external = "sv_v_" + std::to_string(renamed.size());
            renamed[n] = b.make(n->getSort(), native::K::NT_VAR, {}, external);
            symbols[external] = name;
            text += "(declare-const " + external + " " + n->getSort()->toString() + ")\n";
        }
        for (auto n : visited)
            if (n->getKind() == native::K::NT_QUANT_VAR)
                renamed[n] = b.make(n->getSort(), native::K::NT_QUANT_VAR, {},
                                    "sv_b_" + std::to_string(renamed.size()));
        for (auto n : assertions)
            text += "(assert " + SOMTParser::dumpSMTLIB2(native::substitute(n, renamed, memo, b)) +
                    ")\n";
        text += "(check-sat)\n";
        auto file = std::to_string(cases.size()) + ".smt2";
        write(output / file, text);
        cases.push_back({{"input", file},
                         {"group", group},
                         {"heap", heap},
                         {"symbols", symbols},
                         {"expected", result == Result::Sat ? "sat" : "unsat"}});
        write(output / "cases.json", cases.dump(2) + "\n");
    }
};
DecisionOracle decide = [](const NativeAssertions &q) {
    return applications::satisfiability::smt::Solver().solve({q, {}, {}, {}});
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
    auto replay = [&](const v::SafetyAnswer &answer, const std::string &group) {
        if (answer.status != v::SafetyStatus::Safe)
            throw std::runtime_error(group + ": expected safety proof; " + answer.reason);
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
    auto check = [&](const std::string &group, NativeAssertions candidates = {},
                     v::SafetyMethod method = v::SafetyMethod::Induction) {
        replay(v::SafetySolver(decide, {6}, method).solve({s, candidates}), group);
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
    // Completion on an explicitly finite domain, independently checked by BFS
    // in the unit suite. The integer graph above exercises k-induction.
    auto bx = b.make(b.bvSort(2), native::K::NT_VAR, {}, "bx");
    auto bxp = b.make(b.bvSort(2), native::K::NT_VAR, {}, "bxp");
    s.state = {{bx, bxp}};
    s.initial = {b.equal(bx, b.bv(0, 2))};
    s.transition = {b.any({b.all({b.equal(bx, b.bv(0, 2)), b.equal(bxp, b.bv(1, 2))}),
                           b.all({b.equal(bx, b.bv(1, 2)), b.equal(bxp, b.bv(0, 2))})})};
    s.safety = b.negate(b.equal(bx, b.bv(2, 2)));
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
    s = copy;
    auto mode = b.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, "mode");
    auto mp = b.make(SOMTParser::SortManager::getBool(), native::K::NT_VAR, {}, "mp");
    s.state.push_back({mode, mp});
    s.initial.push_back(mode);
    s.transition = {b.equal(mode, mp),
                    b.any({b.negate(mode), b.logical(native::K::NT_GE, {xp, num(0)})})};
    replay(v::ReachabilitySolver(decide, {3}).solve(s), "symbolic-fixed-point");
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
void relations(Export &out) {
    SOMTParser::Parser parser;
    require(parser.parseStr("(set-logic ALL)(declare-heap (Int Int))(declare-const n Int)"
                            "(define-fun-rec p ((n Int)) Bool (or (and (= n 0) sep.emp) "
                            "(and (> n 0) (sep (pto n (- n 1)) (p (- n 1))))))"
                            "(define-fun-rec q ((n Int)) Bool (or (and (<= n 0) sep.emp) "
                            "(and (>= n 1) (sep (q (- n 1)) (pto n (- n 1))))))"
                            "(assert (p n))"),
            "cannot parse relational evidence");
    sl::EntailmentProblem problem;
    auto &c = problem.context;
    c.location = parser.getHeapLocationSort();
    c.data = parser.getHeapDataSort();
    c.declarations = parser.getDeclaredVariables();
    c.assertions = parser.getAssertions();
    c.recursion = sl::RecursiveSemantics::LeastFixedPoint;
    for (const auto &d : parser.getRecursiveDefinitions())
        c.definitions.push_back(
            {d.symbol, d.definition->getFuncBody(), d.definition->getFuncParams()});
    problem.conclusion = parser.mkExpr("(q n)");
    auto result = sl::EntailmentSolver({3000000, 256}).solve(problem);
    require(result.status == sl::EntailmentStatus::Valid && result.certificate,
            "expected predicate inclusion proof");
    require(result.certificate->method == sl::EntailmentProof::StructuralInduction,
            "expected structural induction certificate");
    auto proof = sl::proveRelationalNative(c.location, c.data, c.assertions, problem.conclusion,
                                           c.declarations, c.definitions,
                                           result.certificate->relations, {3000000, 256});
    require(proof.complete && proof.proved, "predicate inclusion replay failed");
    for (const auto &q : proof.obligations)
        out.query(q, Result::Unsat, "sl-relation-premise", true);
    // Independent ground expansions have exact recursive semantics at these
    // arguments. Original recursive equations are not reinterpreted by cvc5.
    native::Nodes b({});
    auto emp = b.logical(native::K::NT_SEP_EMP, {});
    auto p = emp, q = emp;
    for (int n = -1; n <= 4; ++n) {
        if (n > 0) {
            auto cell = b.logical(native::K::NT_SEP_PTO, {b.numeral(n), b.numeral(n - 1)});
            p = b.logical(native::K::NT_SEP_STAR, {cell, p});
            q = b.logical(native::K::NT_SEP_STAR, {q, cell});
        }
        auto pv = n < 0 ? b.boolean(false) : p;
        auto qv = n < 0 ? emp : q;
        auto literal = n < 0 ? "(- 1)" : std::to_string(n);
        auto pc = parser.mkExpr("(p " + literal + ")"), qc = parser.mkExpr("(q " + literal + ")");
        auto cell = b.logical(native::K::NT_SEP_PTO, {b.numeral(100), b.numeral(9)});
        struct Pair {
            native::Node a, z, groundA, groundZ;
        };
        std::size_t pattern = 0;
        for (const auto &item :
             std::vector<Pair>{{pc, qc, pv, qv},
                               {qc, pc, qv, pv},
                               {b.negate(pc), b.negate(qc), b.negate(pv), b.negate(qv)},
                               {b.logical(native::K::NT_SEP_STAR, {cell, pc}), qc,
                                b.logical(native::K::NT_SEP_STAR, {cell, pv}), qv}}) {
            c.assertions = {item.a};
            problem.conclusion = item.z;
            auto checked = sl::EntailmentSolver({3000000, 256}).solve(problem);
            if (checked.status != sl::EntailmentStatus::Valid &&
                checked.status != sl::EntailmentStatus::Invalid)
                throw std::runtime_error("ground relational query n=" + literal + " pattern=" +
                                         std::to_string(pattern) + ": " + checked.reason);
            out.query({item.groundA, b.negate(item.groundZ)},
                      checked.status == sl::EntailmentStatus::Valid ? Result::Unsat : Result::Sat,
                      "sl-exact-ground-expansion-" + literal + "-" + std::to_string(pattern++),
                      true);
        }
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
    relations(out);
    write(out.output / "cases.json", out.cases.dump(2) + "\n");
}
