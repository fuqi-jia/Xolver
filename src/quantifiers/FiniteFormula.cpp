#include "quantifiers/FiniteFormula.h"
#include "quantifiers/bitvector/Circuit.h"
#include <somtparser/ir/node.h>
#include <algorithm>
#include <map>
#include <unordered_map>

namespace xolver::quantifiers {
namespace {
using Node = SOMTParser::Node;
using Kind = SOMTParser::NODE_KIND;
using Bit = boolean::Diagram::Id;
using Word = bitvector::Word;
class Compiler {
    Resources resources_;
    boolean::Diagram diagram_;
    bitvector::Circuit circuit_;
    bool bitvectors_;
    std::unordered_map<Node, Word> bindings_, free_, cache_;
    std::map<std::string, Node> names_;
    void arity(const Node& n, std::size_t count) {
        if (n->getChildrenSize() != count) throw Unsupported("finite-domain operator arity mismatch");
    }
    static mpz_class integer(const Node& node) {
        if (!node || node->getKind() != Kind::NT_CONST)
            throw Unsupported("bit-vector index must be a nonnegative integer constant");
        const auto text = node->getName();
        mpz_class value;
        if (mpz_set_str(value.get_mpz_t(), text.c_str(), 10) || value < 0)
            throw Unsupported("invalid bit-vector index");
        return value;
    }
    std::size_t index(const Node& node) {
        const auto value = integer(node);
        if (!value.fits_ulong_p()) throw Exhausted("bit-vector index exceeds addressable storage");
        return value.get_ui();
    }
    std::size_t width(const Node& n) {
        const auto sort = n->getSort();
        if (sort && sort->isBool()) return 1;
        if (sort && sort->isBv() && bitvectors_) {
            const auto result = sort->getBitWidth();
            if (!result) throw Unsupported("zero-width bit-vector");
            resources_.tick(result);
            return result;
        }
        throw Unsupported("finite-domain solver requires Bool or BitVec sorts");
    }
    Word fresh(const Node& node) {
        Word bits(width(node));
        for (auto& bit : bits) bit = diagram_.variable();
        return bits;
    }
    Bit formula(const Node& n) {
        if (!n || !n->getSort() || !n->getSort()->isBool())
            throw Unsupported("finite-domain assertion must be Boolean");
        return term(n).at(0);
    }
    Word term(const Node& n) {
        Resources::Frame frame(resources_);
        if (!n) throw Unsupported("null finite-domain term");
        const auto kind = n->getKind();
        if (kind == Kind::NT_QUANT_VAR) {
            auto binding = bindings_.find(n);
            if (binding == bindings_.end()) throw Unsupported("unbound finite-domain variable");
            return binding->second;
        }
        if (auto found = cache_.find(n); found != cache_.end()) return found->second;
        Word result = compile(n);
        if (result.size() != width(n)) throw Unsupported("finite-domain result width mismatch");
        cache_.emplace(n, result);
        return result;
    }
    Word compile(const Node& n) {
        const auto kind = n->getKind();
        const auto count = n->getChildrenSize();
        if (kind == Kind::NT_LET || kind == Kind::NT_LET_BIND_VAR || kind == Kind::NT_LET_CHAIN) {
            if (!count) throw Unsupported("empty finite-domain let");
            return term(n->getChild(kind == Kind::NT_LET_CHAIN ? count - 1 : 0));
        }
        if (kind == Kind::NT_VAR) {
            if (auto it = free_.find(n); it != free_.end()) return it->second;
            const auto [it, inserted] = names_.emplace(n->getName(), n);
            if (!inserted && it->second != n) throw Unsupported("ambiguous free symbol identity");
            return free_.emplace(n, fresh(n)).first->second;
        }
        if (kind == Kind::NT_CONST_TRUE) return {1};
        if (kind == Kind::NT_CONST_FALSE) return {0};
        if (kind == Kind::NT_CONST) {
            if (n->getSort()->isBool()) {
                const auto value = n->getValue();
                if (!value || value->getType() != SOMTParser::BOOLEAN)
                    throw Unsupported("invalid Boolean constant");
                return {Bit(value->getBooleanValue())};
            }
            if (!n->getSort()->isBv() || !bitvectors_)
                throw Unsupported("non-finite-domain constant");
            auto text = n->getName();
            int base = 10;
            if (text.starts_with("#b")) { base = 2; text.erase(0, 2); }
            else if (text.starts_with("#x")) { base = 16; text.erase(0, 2); }
            else if (text.starts_with("bv")) text.erase(0, 2);
            mpz_class value;
            if (mpz_set_str(value.get_mpz_t(), text.c_str(), base) || value < 0)
                throw Unsupported("invalid bit-vector literal");
            return circuit_.constant(value, width(n));
        }
        if (kind == Kind::NT_FORALL || kind == Kind::NT_EXISTS) {
            if (count < 2) throw Unsupported("empty finite-domain binder");
            const auto saved = bindings_;
            std::vector<boolean::Diagram::Variable> variables;
            for (std::size_t i = 1; i < count; ++i) {
                const auto binder = n->getChild(i);
                if (binder->getKind() != Kind::NT_QUANT_VAR)
                    throw Unsupported("invalid finite-domain binder");
                auto bits = fresh(binder);
                for (Bit bit : bits) variables.push_back(diagram_.variableOf(bit));
                bindings_[binder] = std::move(bits);
            }
            // Expressions containing bound variables have scope-dependent
            // encodings; a cache cannot cross entry or exit of a binder.
            cache_.clear();
            const auto body = formula(n->getChild(0));
            const auto result = diagram_.eliminate(body, variables, kind == Kind::NT_FORALL);
            bindings_ = saved;
            cache_.clear();
            return {result};
        }
        if (kind == Kind::NT_NOT) { arity(n, 1); return {diagram_.negate(formula(n->getChild(0)))}; }
        if (kind == Kind::NT_AND || kind == Kind::NT_OR || kind == Kind::NT_XOR) {
            Bit result = kind == Kind::NT_AND ? 1 : 0;
            for (auto child : SOMTParser::children(n)) {
                const auto operand = formula(child);
                result = diagram_.apply(kind == Kind::NT_AND ? boolean::Diagram::Op::And :
                    kind == Kind::NT_OR ? boolean::Diagram::Op::Or : boolean::Diagram::Op::Xor,
                    result, operand);
            }
            return {result};
        }
        if (kind == Kind::NT_IMPLIES) {
            if (count < 2) throw Unsupported("implication requires two operands");
            Bit result = formula(n->getChild(count - 1));
            for (std::size_t i = count - 1; i-- > 0;)
                result = diagram_.disjunction(diagram_.negate(formula(n->getChild(i))), result);
            return {result};
        }
        if (kind == Kind::NT_ITE) {
            arity(n, 3);
            const auto condition = formula(n->getChild(0));
            const auto yes = term(n->getChild(1)), no = term(n->getChild(2));
            return circuit_.choose(condition, yes, no);
        }
        if (kind == Kind::NT_EQ || kind == Kind::NT_EQ_BOOL || kind == Kind::NT_EQ_OTHER ||
            kind == Kind::NT_DISTINCT || kind == Kind::NT_DISTINCT_BOOL || kind == Kind::NT_DISTINCT_OTHER) {
            if (count < 2) throw Unsupported("comparison requires two operands");
            const bool distinct = kind == Kind::NT_DISTINCT || kind == Kind::NT_DISTINCT_BOOL ||
                                  kind == Kind::NT_DISTINCT_OTHER;
            std::vector<Word> operands;
            for (auto child : SOMTParser::children(n)) operands.push_back(term(child));
            Bit result = 1;
            for (std::size_t i = 0; i < count; ++i)
                for (std::size_t j = i + 1; j < count; ++j) {
                    if (!distinct && i > 0) break;
                    const auto eq = circuit_.equal(operands[i], operands[j]);
                    result = diagram_.conjunction(result, distinct ? diagram_.negate(eq) : eq);
                }
            return {result};
        }
        if (!bitvectors_ || !count) throw Unsupported("unsupported QBF operator");
        Word a = term(n->getChild(0));
        if (kind == Kind::NT_BV_NOT) { arity(n, 1); return circuit_.invert(a); }
        if (kind == Kind::NT_BV_NEG) { arity(n, 1); return circuit_.negate(a); }
        if (kind == Kind::NT_BV_EXTRACT) {
            arity(n, 3);
            const auto high = index(n->getChild(1)), low = index(n->getChild(2));
            if (high < low || high >= a.size()) throw Unsupported("invalid bit-vector extract bounds");
            return Word(a.begin() + low, a.begin() + high + 1);
        }
        if (kind == Kind::NT_BV_REPEAT || kind == Kind::NT_BV_ZERO_EXT || kind == Kind::NT_BV_SIGN_EXT ||
            kind == Kind::NT_BV_ROTATE_LEFT || kind == Kind::NT_BV_ROTATE_RIGHT) {
            arity(n, 2);
            if (kind == Kind::NT_BV_ROTATE_LEFT || kind == Kind::NT_BV_ROTATE_RIGHT) {
                const mpz_class modulus = integer(n->getChild(1)) % mpz_class(a.size());
                const auto amount = modulus.get_ui();
                Word result(a.size());
                for (std::size_t i = 0; i < a.size(); ++i)
                    result[i] = a[kind == Kind::NT_BV_ROTATE_LEFT ?
                        (i + a.size() - amount) % a.size() : (i + amount) % a.size()];
                return result;
            }
            const auto amount = index(n->getChild(1)), target = width(n);
            if (kind == Kind::NT_BV_REPEAT) {
                if (!amount || target / amount != a.size() || target % amount)
                    throw Unsupported("invalid bit-vector repetition width");
                Word result(target);
                for (std::size_t i = 0; i < target; ++i) result[i] = a[i % a.size()];
                return result;
            }
            if (target < a.size() || target - a.size() != amount)
                throw Unsupported("invalid bit-vector extension width");
            a.resize(target, kind == Kind::NT_BV_SIGN_EXT ? a.back() : 0);
            return a;
        }
        if (kind == Kind::NT_BV_CONCAT) {
            Word result;
            resources_.tick(width(n));
            for (std::size_t i = count; i-- > 0;) {
                auto part = term(n->getChild(i));
                result.insert(result.end(), part.begin(), part.end());
            }
            return result;
        }
        if (kind == Kind::NT_BV_NEGO) {
            arity(n, 1);
            Word minimum(a.size(), 0); minimum.back() = 1;
            return {circuit_.equal(a, minimum)};
        }
        if (count < 2) throw Unsupported("missing bit-vector operand");
        Word b = term(n->getChild(1));
        if (a.size() != b.size()) throw Unsupported("bit-vector operand width mismatch");
        if (kind == Kind::NT_BV_AND || kind == Kind::NT_BV_OR || kind == Kind::NT_BV_XOR ||
            kind == Kind::NT_BV_NAND || kind == Kind::NT_BV_NOR || kind == Kind::NT_BV_XNOR ||
            kind == Kind::NT_BV_ADD || kind == Kind::NT_BV_MUL) {
            for (std::size_t operand = 1; operand < count; ++operand) {
                if (operand > 1) b = term(n->getChild(operand));
                if (a.size() != b.size()) throw Unsupported("bit-vector operand width mismatch");
                if (kind == Kind::NT_BV_ADD) a = circuit_.add(a, b);
                else if (kind == Kind::NT_BV_MUL) a = circuit_.multiply(a, b);
                else for (std::size_t i = 0; i < a.size(); ++i)
                    a[i] = diagram_.apply(kind == Kind::NT_BV_AND || kind == Kind::NT_BV_NAND ?
                        boolean::Diagram::Op::And : kind == Kind::NT_BV_OR || kind == Kind::NT_BV_NOR ?
                        boolean::Diagram::Op::Or : boolean::Diagram::Op::Xor, a[i], b[i]);
            }
            if (kind == Kind::NT_BV_NAND || kind == Kind::NT_BV_NOR || kind == Kind::NT_BV_XNOR)
                a = circuit_.invert(a);
            return a;
        }
        arity(n, 2);
        if (kind == Kind::NT_BV_SUB) return circuit_.subtract(a, b);
        if (kind == Kind::NT_BV_COMP) return {circuit_.equal(a, b)};
        if (kind == Kind::NT_BV_SHL || kind == Kind::NT_BV_LSHR || kind == Kind::NT_BV_ASHR)
            return circuit_.shift(a, b, kind == Kind::NT_BV_SHL, kind == Kind::NT_BV_ASHR);
        if (kind == Kind::NT_BV_ULT || kind == Kind::NT_BV_ULE || kind == Kind::NT_BV_UGT || kind == Kind::NT_BV_UGE ||
            kind == Kind::NT_BV_SLT || kind == Kind::NT_BV_SLE || kind == Kind::NT_BV_SGT || kind == Kind::NT_BV_SGE) {
            const bool isSigned = kind == Kind::NT_BV_SLT || kind == Kind::NT_BV_SLE || kind == Kind::NT_BV_SGT || kind == Kind::NT_BV_SGE;
            if (kind == Kind::NT_BV_UGT || kind == Kind::NT_BV_UGE || kind == Kind::NT_BV_SGT || kind == Kind::NT_BV_SGE)
                std::swap(a, b);
            const Bit lt = circuit_.less(a, b, isSigned);
            const bool inclusive = kind == Kind::NT_BV_ULE || kind == Kind::NT_BV_UGE || kind == Kind::NT_BV_SLE || kind == Kind::NT_BV_SGE;
            return {inclusive ? diagram_.disjunction(lt, circuit_.equal(a, b)) : lt};
        }
        if (kind == Kind::NT_BV_UDIV || kind == Kind::NT_BV_UREM || kind == Kind::NT_BV_UMOD) {
            auto [quotient, remainder] = circuit_.divide(a, b);
            return kind == Kind::NT_BV_UDIV ? quotient : remainder;
        }
        if (kind == Kind::NT_BV_SDIV || kind == Kind::NT_BV_SREM || kind == Kind::NT_BV_SMOD) {
            const auto absA = circuit_.choose(a.back(), circuit_.negate(a), a);
            const auto absB = circuit_.choose(b.back(), circuit_.negate(b), b);
            auto [quotient, remainder] = circuit_.divide(absA, absB);
            const auto opposite = diagram_.exclusiveOr(a.back(), b.back());
            if (kind == Kind::NT_BV_SDIV)
                return circuit_.choose(opposite, circuit_.negate(quotient), quotient);
            remainder = circuit_.choose(a.back(), circuit_.negate(remainder), remainder);
            if (kind == Kind::NT_BV_SMOD) {
                const auto nonzero = diagram_.negate(circuit_.equal(remainder, circuit_.constant(0, a.size())));
                remainder = circuit_.choose(diagram_.conjunction(opposite, nonzero), circuit_.add(remainder, b), remainder);
            }
            return remainder;
        }
        if (kind == Kind::NT_BV_SDIVO) {
            Word minimum(a.size(), 0); minimum.back() = 1;
            return {diagram_.conjunction(circuit_.equal(a, minimum), circuit_.equal(b, circuit_.constant(-1, a.size())))};
        }
        if (kind == Kind::NT_BV_UADDO || kind == Kind::NT_BV_SADDO ||
            kind == Kind::NT_BV_UMULO || kind == Kind::NT_BV_SMULO) {
            const auto original = a.size();
            const bool isSigned = kind == Kind::NT_BV_SADDO || kind == Kind::NT_BV_SMULO;
            const bool multiply = kind == Kind::NT_BV_UMULO || kind == Kind::NT_BV_SMULO;
            resources_.tick(original);
            if (original > std::numeric_limits<std::size_t>::max() / 2)
                throw Exhausted("bit-vector product exceeds addressable storage");
            const auto extended = multiply ? 2 * original : original + 1;
            a.resize(extended, isSigned ? a.back() : 0);
            b.resize(extended, isSigned ? b.back() : 0);
            const auto value = multiply ? circuit_.multiply(a, b) : circuit_.add(a, b);
            Bit overflow = 0;
            for (std::size_t i = original; i < value.size(); ++i)
                overflow = diagram_.disjunction(overflow, diagram_.exclusiveOr(value[i], isSigned ? value[original - 1] : 0));
            return {overflow};
        }
        throw Unsupported("unsupported quantified bit-vector operator");
    }
public:
    Compiler(Limits limits, bool bitvectors)
        : resources_(limits), diagram_(resources_), circuit_(diagram_), bitvectors_(bitvectors) {}
    SolverAnswer solve(const Roots& roots) {
        Bit result = 1;
        for (const auto& root : roots) result = diagram_.conjunction(result, formula(root));
        SolverAnswer answer;
        answer.result = result == 0 ? Result::Unsat : Result::Sat;
        if (result != 0) {
            auto values = diagram_.witness(result);
            if (!diagram_.evaluate(result, values)) throw std::logic_error("BDD witness violates eliminated formula");
            answer.model.emplace();
            for (const auto& [node, bits] : free_) {
                mpz_class value = 0;
                for (std::size_t i = 0; i < bits.size(); ++i)
                    if (values.at(diagram_.variableOf(bits[i]))) mpz_setbit(value.get_mpz_t(), i);
                answer.model->assignments.emplace(node->getName(), node->getSort()->isBool() ?
                    (value == 0 ? "false" : "true") : "(_ bv" + value.get_str() + " " + std::to_string(bits.size()) + ")");
            }
        }
        return answer;
    }
};
}
SolverAnswer solveFinite(const Roots& roots, Limits limits, bool bitvectors) {
    try { return Compiler(limits, bitvectors).solve(roots); }
    catch (const Exhausted& error) { SolverAnswer answer; answer.reason = error.what(); return answer; }
    catch (const Unsupported& error) { SolverAnswer answer; answer.reason = error.what(); return answer; }
    catch (const std::bad_alloc&) { SolverAnswer answer; answer.reason = "quantifier memory exhausted"; return answer; }
}
SolverAnswer boolean::solve(const Roots& roots, Limits limits) { return solveFinite(roots, limits, false); }
SolverAnswer bitvector::solve(const Roots& roots, Limits limits) { return solveFinite(roots, limits, true); }
}
