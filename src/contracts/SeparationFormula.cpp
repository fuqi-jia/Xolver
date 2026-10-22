#include "contracts/SeparationFormula.h"
#include "base/IntegerLiteral.h"
#include <algorithm>
#include <limits>
#include <set>

namespace xolver::sl {
namespace {
FormulaId append(Formula& f, FormulaNode node) {
    f.nodes.push_back(std::move(node));
    return f.root = f.nodes.size() - 1;
}
FormulaId binary(Formula& f, FormulaNode::Kind kind, FormulaId a, FormulaId b) {
    FormulaNode node;
    node.kind = kind; node.children = {a, b};
    return append(f, std::move(node));
}
}
FormulaId Formula::boolean(bool value) {
    FormulaNode node; node.boolean = value; return append(*this, std::move(node));
}
FormulaId Formula::relation(Location a, Location b, bool equal) {
    FormulaNode node; node.kind = FormulaNode::Kind::Relation;
    node.relation = {a, b, equal}; return append(*this, std::move(node));
}
FormulaId Formula::emp() {
    FormulaNode node; node.kind = FormulaNode::Kind::Emp;
    return append(*this, std::move(node));
}
FormulaId Formula::pointsTo(Location a, std::vector<Field> fields) {
    FormulaNode node; node.kind = FormulaNode::Kind::PointsTo;
    node.cell = {a, std::move(fields)}; return append(*this, std::move(node));
}
FormulaId Formula::negate(FormulaId a) {
    FormulaNode node; node.kind = FormulaNode::Kind::Not; node.children = {a};
    return append(*this, std::move(node));
}
FormulaId Formula::conjunction(FormulaId a, FormulaId b) {
    return binary(*this, FormulaNode::Kind::And, a, b);
}
FormulaId Formula::disjunction(FormulaId a, FormulaId b) {
    return binary(*this, FormulaNode::Kind::Or, a, b);
}
FormulaId Formula::star(FormulaId a, FormulaId b) {
    return binary(*this, FormulaNode::Kind::Star, a, b);
}
FormulaId Formula::wand(FormulaId a, FormulaId b) {
    return binary(*this, FormulaNode::Kind::Wand, a, b);
}
}

namespace xolver::sl::detail {
namespace {
void canonicalInteger(std::string& text) {
    mpz_class value;
    if (!integerLiteral(text, value)) throw Stop("invalid integer heap field");
    text = value.get_str();
}
void signature(const Formula& f, const Record& record) {
    if (record.size() != f.fieldSorts.size()) throw Stop("heap record arity mismatch");
    for (std::size_t i = 0; i < record.size(); ++i)
        if ((f.fieldSorts[i] == FieldSort::Location) !=
            std::holds_alternative<uint64_t>(record[i]))
            throw Stop("heap record sort mismatch");
}
}

Prepared prepare(const Formula& input, Work& work) {
    if (input.root >= input.nodes.size()) throw Stop("invalid spatial formula root");
    work.tick(input.nodes.size());
    Prepared p{input, {}, {}, std::vector<bool>(input.nodes.size())};
    for (auto sort : input.fieldSorts)
        if (sort != FieldSort::Location && sort != FieldSort::Integer)
            throw Stop("invalid heap field sort");
    std::vector<std::size_t> depths;
    for (std::size_t i = 0; i < p.formula.nodes.size(); ++i) {
        work.tick();
        auto& n = p.formula.nodes[i];
        using K = FormulaNode::Kind;
        std::size_t arity = 0, width = 0, depth = 1;
        switch (n.kind) {
        case K::Boolean: break;
        case K::Relation: break;
        case K::Emp: width = 1; break;
        case K::PointsTo:
            width = 1;
            if (n.cell.fields.size() != input.fieldSorts.size())
                throw Stop("points-to arity mismatch");
            for (std::size_t j = 0; j < n.cell.fields.size(); ++j) {
                work.tick();
                auto& field = n.cell.fields[j];
                if ((input.fieldSorts[j] == FieldSort::Location) !=
                    std::holds_alternative<Location>(field))
                    throw Stop("points-to sort mismatch");
                if (auto text = std::get_if<std::string>(&field)) {
                    work.tick(text->size());
                    canonicalInteger(*text);
                }
            }
            break;
        case K::Not: arity = 1; break;
        case K::And: case K::Or: case K::Star: case K::Wand: arity = 2; break;
        default: throw Stop("invalid spatial connective");
        }
        if (n.children.size() != arity) throw Stop("spatial connective arity mismatch");
        for (auto child : n.children) {
            if (child >= i) throw Stop("spatial formula is not topologically ordered");
            depth = std::max(depth, depths[child] + 1);
            width = std::max(width, p.width[child]);
        }
        if (depth > work.limits.maxDepth) throw Stop("separation logic depth limit");
        if (n.kind == K::Star) {
            const auto a = p.width[n.children[0]], b = p.width[n.children[1]];
            if (a > std::numeric_limits<std::size_t>::max() - b)
                throw Stop("spatial width overflow");
            width = a + b;
        }
        if (n.kind == K::Wand) width = p.width[n.children[1]];
        p.width.push_back(width); depths.push_back(depth);
    }
    p.reachable[input.root] = true;
    std::set<Location> symbols{0};
    for (std::size_t i = input.root + 1; i > 0;) {
        --i;
        if (!p.reachable[i]) continue;
        const auto& n = p.formula.nodes[i];
        for (auto child : n.children) p.reachable[child] = true;
        if (n.kind == FormulaNode::Kind::Relation) {
            symbols.insert(n.relation.left); symbols.insert(n.relation.right);
        } else if (n.kind == FormulaNode::Kind::PointsTo) {
            symbols.insert(n.cell.address);
            for (const auto& field : n.cell.fields)
                if (auto loc = std::get_if<Location>(&field)) symbols.insert(*loc);
        }
    }
    p.symbols.assign(symbols.begin(), symbols.end());
    return p;
}

Record instantiate(const PointsTo& cell, const std::map<Location, uint64_t>& stack) {
    Record record;
    for (const auto& field : cell.fields) {
        if (auto loc = std::get_if<Location>(&field)) record.emplace_back(stack.at(*loc));
        else record.emplace_back(std::get<std::string>(field));
    }
    return record;
}

Vocabulary vocabulary(const Prepared& p, const std::map<Location, uint64_t>& stack, Work& work) {
    std::set<uint64_t> addresses;
    for (auto symbol : p.symbols) {
        work.tick();
        auto it = stack.find(symbol);
        if (it == stack.end()) throw Stop("missing location interpretation");
        if (symbol == 0 && it->second != 0) throw Stop("nil interpretation is not zero");
        if (it->second != 0) addresses.insert(it->second);
    }
    std::set<Record> records;
    for (std::size_t i = 0; i < p.formula.nodes.size(); ++i) {
        if (!p.reachable[i]) continue;
        work.tick();
        const auto& n = p.formula.nodes[i];
        if (n.kind == FormulaNode::Kind::PointsTo) records.insert(instantiate(n.cell, stack));
    }
    Record other;
    for (auto sort : p.formula.fieldSorts) {
        if (sort == FieldSort::Location) other.emplace_back(uint64_t{0});
        else other.emplace_back(std::string("0"));
    }
    // An empty tuple has only one possible value. Every nonempty signature has
    // an infinite component; a value outside the finitely mentioned records
    // represents every record no points-to atom can distinguish.
    if (!other.empty()) {
        uint64_t candidate = 0;
        while (records.count(other)) {
            work.tick();
            if (candidate == std::numeric_limits<uint64_t>::max())
                throw Stop("heap value representative overflow");
            ++candidate;
            if (p.formula.fieldSorts.front() == FieldSort::Location) other[0] = candidate;
            else other[0] = std::to_string(candidate);
        }
    }
    records.insert(std::move(other));
    return {{addresses.begin(), addresses.end()}, {records.begin(), records.end()}};
}

Heap canonicalHeap(const Prepared& p, const Model& model, Work& work) {
    work.tick(model.heap.size());
    Heap heap = model.heap;
    for (auto& [address, record] : heap) {
        work.tick();
        if (address == 0) throw Stop("nil is allocated");
        signature(p.formula, record);
        for (auto& field : record) {
            work.tick();
            if (auto text = std::get_if<std::string>(&field)) {
                work.tick(text->size());
                canonicalInteger(*text);
            }
        }
    }
    return heap;
}

std::vector<uint64_t> freshAddresses(const Vocabulary& v, const Heap& heap,
                                    std::size_t count, Work& work) {
    std::vector<uint64_t> result;
    uint64_t next = 0;
    while (result.size() < count) {
        work.tick();
        if (next == std::numeric_limits<uint64_t>::max())
            throw Stop("heap address representative overflow");
        ++next;
        if (!heap.count(next) && !std::binary_search(v.addresses.begin(), v.addresses.end(), next))
            result.push_back(next);
    }
    return result;
}
} // namespace xolver::sl::detail
