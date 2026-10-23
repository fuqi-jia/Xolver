#pragma once
#include "base/WorkBudget.h"
#include <somtparser/ir/node.h>
#include <gmpxx.h>
#include <set>

namespace xolver::native {
using Node = SOMTParser::Node;
using Sort = std::shared_ptr<SOMTParser::Sort>;
using K = SOMTParser::NODE_KIND;
struct Unsupported : std::runtime_error { using std::runtime_error::runtime_error; };
class Nodes {
    SOMTParser::SortManager sorts_;
    std::set<std::string> names_;
    std::size_t next_ = 0;
    std::size_t depth_ = 0;
public:
    class Frame {
        Nodes& owner_;
    public:
        explicit Frame(Nodes& owner):owner_(owner) {
            owner_.budget.tick();
            if (owner_.depth_>=512) throw ResourceExhausted("native lowering depth exhausted");
            ++owner_.depth_;
        }
        ~Frame(){--owner_.depth_;}
        Frame(const Frame&)=delete;
    };
    WorkBudget budget;
    explicit Nodes(const std::vector<Node>& roots, std::size_t work = 2000000) : budget(work) {
        std::vector<Node> pending = roots;
        std::set<Node> seen;
        while (!pending.empty()) {
            auto n = pending.back(); pending.pop_back();
            if (!n || !seen.insert(n).second) continue;
            budget.tick(); names_.insert(n->getName());
            for (auto c : SOMTParser::children(n)) pending.push_back(c);
        }
    }
    Sort bvSort(std::size_t width) { return sorts_.createBVSort(width); }
    Node make(Sort sort, K kind, std::vector<Node> args, std::string name = {}) {
        budget.tick();
        if (name.empty()) name = SOMTParser::kindToString(kind);
        return std::make_shared<SOMTParser::DAGNode>(sort, kind, std::move(name), std::move(args));
    }
    Node fresh(Sort sort) {
        std::string name;
        do { name = "@xolver.finite." + std::to_string(next_++); } while (!names_.insert(name).second);
        return make(sort, K::NT_VAR, {}, name);
    }
    Node boolean(bool value) { return make(SOMTParser::SortManager::getBool(), value ? K::NT_CONST_TRUE : K::NT_CONST_FALSE, {}, value ? "true" : "false"); }
    Node numeral(std::size_t value) { return make(SOMTParser::SortManager::getInt(), K::NT_CONST, {}, std::to_string(value)); }
    Node bv(const mpz_class& value, std::size_t width) {
        budget.tick(width);
        if (!width) throw Unsupported("zero-width bit-vector");
        std::string text = "#b";
        for (std::size_t i = width; i-- > 0;) text += mpz_tstbit(value.get_mpz_t(), i) ? '1' : '0';
        return make(bvSort(width), K::NT_CONST, {}, text);
    }
    Node logical(K kind, std::vector<Node> args) { return make(SOMTParser::SortManager::getBool(), kind, std::move(args)); }
    Node equal(Node a, Node b) { return logical(K::NT_EQ, {a,b}); }
    Node negate(Node a) { return logical(K::NT_NOT, {a}); }
    Node all(std::vector<Node> args) { return args.empty() ? boolean(true) : logical(K::NT_AND, std::move(args)); }
    Node any(std::vector<Node> args) { return args.empty() ? boolean(false) : logical(K::NT_OR, std::move(args)); }
    Node choose(Node c, Node a, Node b) { return make(a->getSort(), K::NT_ITE, {c,a,b}); }
    Node extract(Node x, std::size_t high, std::size_t low) {
        return make(bvSort(high-low+1), K::NT_BV_EXTRACT, {x,numeral(high),numeral(low)});
    }
    Node concat(Node a, Node b) {
        return make(bvSort(a->getSort()->getBitWidth()+b->getSort()->getBitWidth()),K::NT_BV_CONCAT,{a,b});
    }
};
}
