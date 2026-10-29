#include "applications/satisfiability/smt/common/finite/Solver.h"
#include "ir/NativeBuilder.h"
#include "quantifiers/FiniteFormula.h"
#include <limits>
#include <map>

namespace xolver::applications::satisfiability::smt::finite {
namespace {
using namespace xolver::native;
struct Value {
    Sort sort;
    std::vector<Node> cells;
};
class Lowering {
    Nodes nodes;
    std::map<Node, Value> memo, variables;
    struct Apply {
        Node input, output;
        std::vector<Node> args;
    };
    std::vector<Apply> functions;
    NativeAssertions constraints;
    std::set<std::string> freeNames;
    static bool scalar(Sort s) { return s && (s->isBool() || s->isBv()); }
    std::size_t size(Sort s) {
        if (scalar(s))
            return 1;
        if (!s || !s->isArray() || !scalar(s->getElemSort()) || !scalar(s->getIndexSort()))
            throw Unsupported("finite arrays require Bool/BitVec indices and elements");
        auto index = s->getIndexSort();
        const auto bits = index->isBool() ? 1 : index->getBitWidth();
        if (bits >= std::numeric_limits<std::size_t>::digits)
            throw ResourceExhausted("finite array domain exceeds addressable storage");
        const auto n = std::size_t(1) << bits;
        nodes.budget.tick(n);
        return n;
    }
    Node index(Sort s, std::size_t i) {
        return s->isBool() ? nodes.boolean(i != 0) : nodes.bv(mpz_class(i), s->getBitWidth());
    }
    Node one(Node n) {
        auto v = lower(n);
        if (!scalar(v.sort) || v.cells.size() != 1)
            throw Unsupported("expected finite scalar");
        return v.cells.front();
    }
    Node equality(const Value &a, const Value &b) {
        if (!(*a.sort == *b.sort) || a.cells.size() != b.cells.size())
            throw Unsupported("finite equality sort mismatch");
        std::vector<Node> terms;
        for (std::size_t i = 0; i < a.cells.size(); ++i)
            terms.push_back(nodes.equal(a.cells[i], b.cells[i]));
        return nodes.all(std::move(terms));
    }
    Value lower(Node n) {
        Nodes::Frame frame(nodes);
        nodes.budget.tick();
        if (!n || !n->getSort())
            throw Unsupported("null finite term");
        if (auto it = memo.find(n); it != memo.end())
            return it->second;
        const auto k = n->getKind();
        const auto count = n->getChildrenSize();
        const auto sort = n->getSort();
        if (k == K::NT_FORALL || k == K::NT_EXISTS || k == K::NT_QUANT_VAR)
            throw Unsupported("quantified arrays/UF need a binder-aware combination backend");
        Value result{sort, {}};
        if (k == K::NT_LET || k == K::NT_LET_CHAIN || k == K::NT_LET_BIND_VAR) {
            if (!count)
                throw Unsupported("empty let");
            result = lower(n->getChild(k == K::NT_LET_CHAIN ? count - 1 : 0));
        } else if (k == K::NT_VAR) {
            if (!freeNames.insert(n->getName()).second)
                throw Unsupported("ambiguous free symbol identity");
            for (std::size_t i = 0, length = size(sort); i < length; ++i)
                result.cells.push_back(nodes.fresh(sort->isArray() ? sort->getElemSort() : sort));
            variables[n] = result;
        } else if (k == K::NT_UF_APPLY) {
            if (!scalar(sort))
                throw Unsupported("UF result must be Bool/BitVec");
            Apply app{n, nodes.fresh(sort), {}};
            for (auto c : SOMTParser::children(n))
                app.args.push_back(one(c));
            for (const auto &previous : functions)
                if (previous.input->getName() == n->getName()) {
                    if (previous.args.size() != app.args.size() ||
                        !(*previous.output->getSort() == *sort))
                        throw Unsupported("ambiguous UF signature");
                    std::vector<Node> equal;
                    for (std::size_t i = 0; i < app.args.size(); ++i) {
                        if (!(*app.args[i]->getSort() == *previous.args[i]->getSort()))
                            throw Unsupported("UF argument sort mismatch");
                        equal.push_back(nodes.equal(app.args[i], previous.args[i]));
                    }
                    constraints.push_back(
                        nodes.logical(K::NT_IMPLIES, {nodes.all(equal),
                                                      nodes.equal(app.output, previous.output)}));
                }
            result.cells = {app.output};
            functions.push_back(std::move(app));
        } else if (k == K::NT_SELECT) {
            if (count != 2)
                throw Unsupported("select arity");
            auto array = lower(n->getChild(0));
            auto at = one(n->getChild(1));
            if (!array.sort->isArray())
                throw Unsupported("select requires array");
            Node selected = array.cells.back();
            for (std::size_t i = array.cells.size() - 1; i-- > 0;)
                selected = nodes.choose(nodes.equal(at, index(array.sort->getIndexSort(), i)),
                                        array.cells[i], selected);
            result.cells = {selected};
        } else if (k == K::NT_STORE) {
            if (count != 3)
                throw Unsupported("store arity");
            result = lower(n->getChild(0));
            auto at = one(n->getChild(1)), value = one(n->getChild(2));
            if (!result.sort->isArray())
                throw Unsupported("store requires array");
            for (std::size_t i = 0; i < result.cells.size(); ++i)
                result.cells[i] = nodes.choose(nodes.equal(at, index(sort->getIndexSort(), i)),
                                               value, result.cells[i]);
        } else if (sort->isArray() && k == K::NT_CONST_ARRAY) {
            if (count != 1)
                throw Unsupported("constant array arity");
            result.cells.assign(size(sort), one(n->getChild(0)));
        } else if (k == K::NT_ITE) {
            if (count != 3)
                throw Unsupported("ite arity");
            auto condition = one(n->getChild(0));
            auto yes = lower(n->getChild(1)), no = lower(n->getChild(2));
            if (!(*yes.sort == *no.sort) || yes.cells.size() != no.cells.size())
                throw Unsupported("ite sort mismatch");
            for (std::size_t i = 0; i < yes.cells.size(); ++i)
                result.cells.push_back(nodes.choose(condition, yes.cells[i], no.cells[i]));
        } else if (k == K::NT_EQ || k == K::NT_EQ_OTHER || k == K::NT_EQ_BOOL ||
                   k == K::NT_DISTINCT || k == K::NT_DISTINCT_OTHER || k == K::NT_DISTINCT_BOOL) {
            if (count < 2)
                throw Unsupported("equality arity");
            const bool distinct =
                k == K::NT_DISTINCT || k == K::NT_DISTINCT_OTHER || k == K::NT_DISTINCT_BOOL;
            std::vector<Value> values;
            for (auto c : SOMTParser::children(n))
                values.push_back(lower(c));
            std::vector<Node> terms;
            for (std::size_t i = 0; i < count; ++i)
                for (std::size_t j = i + 1; j < count; ++j) {
                    if (!distinct && i)
                        break;
                    auto eq = equality(values[i], values[j]);
                    terms.push_back(distinct ? nodes.negate(eq) : eq);
                }
            result.cells = {nodes.all(terms)};
        } else {
            // Index numerals are preserved; the finite compiler checks every
            // actual operator and rejects all unsupported arithmetic signatures.
            if ((sort->isInt() || sort->isIntOrReal()) && k == K::NT_CONST)
                return {sort, {n}};
            if (!scalar(sort))
                throw Unsupported("unsupported finite combination sort");
            std::vector<Node> args;
            for (auto c : SOMTParser::children(n)) {
                if (c->getKind() == K::NT_CONST &&
                    (c->getSort()->isInt() || c->getSort()->isIntOrReal()))
                    args.push_back(c);
                else
                    args.push_back(one(c));
            }
            result.cells = {nodes.make(sort, k, args, n->getName())};
        }
        memo.emplace(n, result);
        return result;
    }
    static std::string value(Node n, const TheoryModel &model) {
        auto text = quantifiers::finiteValue(n, model);
        if (!text)
            throw Unsupported("finite model reconstruction failed");
        return *text;
    }
    static std::string token(Node n, const TheoryModel &model) {
        const auto text = value(n, model);
        // Share Boolean tokens with the independent array model checker.
        return n->getSort()->isBool() ? (text == "true" ? "#b:1" : "#b:0") : "#smt:" + text;
    }

  public:
    Lowering(const NativeAssertions &roots, std::size_t work) : nodes(roots, work) {}
    SolverAnswer solve(const NativeAssertions &roots, quantifiers::Limits limits) {
        for (auto root : roots)
            constraints.push_back(one(root));
        auto answer = quantifiers::bitvector::solve(constraints, limits);
        if (answer.result != Result::Sat || !answer.model)
            return answer;
        const auto encoded = *answer.model;
        answer.model.emplace();
        for (const auto &[input, v] : variables) {
            if (scalar(v.sort))
                answer.model->assignments[input->getName()] = value(v.cells[0], encoded);
            else {
                TheoryModel::ArrayInterp array;
                array.indexSort = v.sort->getIndexSort()->toString();
                array.elemSort = v.sort->getElemSort()->toString();
                array.defaultVal = token(v.cells[0], encoded);
                for (std::size_t i = 1; i < v.cells.size(); ++i)
                    array.entries.emplace_back(token(index(v.sort->getIndexSort(), i), encoded),
                                               token(v.cells[i], encoded));
                answer.model->arrayInterps[input->getName()] = std::move(array);
            }
        }
        for (const auto &app : functions) {
            auto &f = answer.model->functionInterps[app.input->getName()];
            if (f.retSort.empty()) {
                f.retSort = app.output->getSort()->toString();
                for (auto arg : app.args)
                    f.argSorts.push_back(arg->getSort()->toString());
                f.deflt = token(app.output, encoded);
            }
            TheoryModel::FuncEntry entry;
            for (auto arg : app.args)
                entry.args.push_back(token(arg, encoded));
            entry.value = token(app.output, encoded);
            f.entries.push_back(std::move(entry));
        }
        return answer;
    }
};
} // namespace
SolverAnswer solve(const NativeAssertions &roots, quantifiers::Limits limits) {
    try {
        return Lowering(roots, limits.work).solve(roots, limits);
    } catch (const Unsupported &e) {
        SolverAnswer r;
        r.reason = e.what();
        return r;
    } catch (const ResourceExhausted &e) {
        SolverAnswer r;
        r.reason = e.what();
        return r;
    } catch (const std::bad_alloc &) {
        SolverAnswer r;
        r.reason = "finite combination memory exhausted";
        return r;
    }
}
} // namespace xolver::applications::satisfiability::smt::finite
