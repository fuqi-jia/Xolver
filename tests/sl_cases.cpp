#include "xolver/SeparationLogic.h"
#include <nlohmann/json.hpp>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <random>
#include <set>
#include <stdexcept>
using namespace xolver;
using namespace xolver::sl;
using Json = nlohmann::json;
namespace {
const std::string preamble =
    // Int fixes an infinite address domain. These formulas use only location
    // equality, so no arithmetic semantics is imposed on abstract addresses.
    "(set-logic QF_ALL)\n(define-sort L () Int)\n(declare-heap (L Int))\n"
    "(declare-const x L)\n(declare-const y L)\n";
std::string location(Location id) {
    if (id == 0) return "(as sep.nil L)";
    if (id == 1) return "x";
    if (id == 2) return "y";
    throw std::invalid_argument("unexpected generated location");
}
std::string emit(const Formula& f, FormulaId id) {
    const auto& n = f.nodes.at(id);
    using K = FormulaNode::Kind;
    switch (n.kind) {
    case K::Boolean: return n.boolean ? "true" : "false";
    case K::Emp: return "sep.emp";
    case K::Relation:
        return "(" + std::string(n.relation.equal ? "=" : "distinct") + " " +
            location(n.relation.left) + " " + location(n.relation.right) + ")";
    case K::PointsTo:
        return "(pto " + location(n.cell.address) + " " +
            std::get<std::string>(n.cell.fields.at(0)) + ")";
    default: break;
    }
    std::string op;
    switch (n.kind) {
    case K::Not: op = "not"; break;
    case K::And: op = "and"; break;
    case K::Or: op = "or"; break;
    case K::Star: op = "sep"; break;
    case K::Wand: op = "wand"; break;
    default: throw std::invalid_argument("unexpected generated operator");
    }
    std::string result = "(" + op;
    for (auto child : n.children) result += " " + emit(f, child);
    return result + ")";
}
std::string name(uint64_t address) {
    return address == 0 ? "(as sep.nil L)" : "m" + std::to_string(address);
}
std::string pin(const Model& m) {
    std::set<uint64_t> values{0};
    for (auto [ignored, value] : m.locations) values.insert(value);
    for (const auto& [address, ignored] : m.heap) values.insert(address);
    std::string out;
    for (auto value : values)
        if (value) out += "(declare-const " + name(value) + " L)\n";
    if (values.size() > 1) {
        out += "(assert (distinct";
        for (auto value : values) out += " " + name(value);
        out += "))\n";
    }
    for (auto [symbol, value] : m.locations)
        out += "(assert (= " + location(symbol) + " " + name(value) + "))\n";
    out += "(assert ";
    if (m.heap.empty()) out += "sep.emp";
    else {
        if (m.heap.size() > 1) out += "(sep";
        for (const auto& [address, record] : m.heap)
            out += " (pto " + name(address) + " " + std::get<std::string>(record.at(0)) + ")";
        if (m.heap.size() > 1) out += ")";
    }
    return out + ")\n";
}
void write(const std::filesystem::path& path, const std::string& text) {
    std::ofstream file(path);
    file.exceptions(std::ios::failbit | std::ios::badbit);
    file << text;
}
}
int main(int argc, char** argv) {
    if (argc != 2) return 2;
    const std::filesystem::path output(argv[1]);
    if (!std::filesystem::create_directory(output)) return 3;
    std::mt19937 random(20261021);
    Json cases = Json::array();
    for (unsigned trial = 0; trial < 240; ++trial) {
        Formula f({FieldSort::Integer});
        f.emp(); f.boolean(true); f.boolean(false);
        f.pointsTo(1, {std::string("0")});
        f.pointsTo(1, {std::string("1")});
        f.pointsTo(2, {std::string("0")});
        f.pointsTo(0, {std::string("0")});
        f.relation(1, 2); f.relation(1, 0, false);
        for (unsigned i = 0; i < 7; ++i) {
            const auto a = random() % f.nodes.size(), b = random() % f.nodes.size();
            switch (random() % 5) {
            case 0: f.negate(a); break;
            case 1: f.conjunction(a, b); break;
            case 2: f.disjunction(a, b); break;
            case 3: f.star(a, b); break;
            case 4: f.wand(a, b); break;
            }
        }
        const auto source = preamble + "(assert " + emit(f, f.root) + ")\n";
        const auto prefix = "case-" + std::to_string(trial);
        write(output / (prefix + ".smt2"), source + "(check-sat)\n");
        const auto start = std::chrono::steady_clock::now();
        auto result = solve(f, {2000000, 256});
        const auto elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - start).count();
        const char* verdict = result.result == Result::Sat ? "sat" :
            result.result == Result::Unsat ? "unsat" : "unknown";
        Json record{{"input", prefix + ".smt2"}, {"result", verdict},
                    {"seconds", elapsed}, {"reason", result.reason}};
        if (result.result == Result::Sat) {
            const auto modelFile = prefix + "-model.smt2";
            write(output / modelFile, source + pin(result.model) + "(check-sat)\n");
            record["model"] = modelFile;
        }
        cases.push_back(std::move(record));
    }
    write(output / "candidate.json", cases.dump(2) + "\n");
}
