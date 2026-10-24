#include "applications/sv/verification/Range.h"
#include "algebra/interval/IntervalOperations.h"
#include "base/MpqUtils.h"
#include "ir/NativeBuilder.h"
#include <map>
#include <set>

namespace xolver::applications::sv::verification {
namespace {
using namespace native;
using Box = std::map<Node, RangeBound>;
enum class Truth { Yes, No, Open };
Truth invert(Truth t) {
    return t == Truth::Yes ? Truth::No : t == Truth::No ? Truth::Yes : Truth::Open;
}
struct Engine {
    Nodes nodes;
    std::set<Node> assumptions;
    Box box;
    explicit Engine(const Obligation &o, std::size_t limit)
        : nodes(
              [&] {
                  auto roots = o.assumptions;
                  roots.push_back(o.conclusion);
                  return roots;
              }(),
              limit) {
        if (!o.conclusion || !o.conclusion->getSort() || !o.conclusion->getSort()->isBool())
            throw std::invalid_argument("range conclusion must be Boolean");
        for (auto a : o.assumptions)
            collect(a);
    }
    void collect(Node n) {
        Nodes::Frame frame(nodes);
        if (!n || !n->getSort() || !n->getSort()->isBool())
            throw std::invalid_argument("range assumptions must be Boolean");
        if (n->getKind() == K::NT_AND)
            for (auto c : SOMTParser::children(n))
                collect(c);
        else
            assumptions.insert(n);
    }
    bool nonzero(Node n, bool constantsOnly) {
        Nodes::Frame frame(nodes);
        if (constantsOnly)
            return false;
        // Only mandatory assumptions justify excluding zero. In particular,
        // finding a disequality under a disjunction is not sufficient.
        for (auto a : assumptions) {
            nodes.budget.tick();
            auto eq = a;
            if (a->getKind() == K::NT_NOT && a->getChildrenSize() == 1 &&
                a->getChild(0)->getKind() == K::NT_EQ)
                eq = a->getChild(0);
            else if (a->getKind() != K::NT_DISTINCT)
                continue;
            if (eq->getChildrenSize() != 2)
                continue;
            for (std::size_t i = 0; i < 2; ++i)
                if (eq->getChild(i) == n) {
                    auto other = interval(eq->getChild(1 - i), true);
                    if (other && other->lo == 0 && other->hi == 0)
                        return true;
                }
        }
        if (n->getKind() == K::NT_NEG && n->getChildrenSize() == 1)
            return nonzero(n->getChild(0), false);
        if (n->getKind() == K::NT_ITE && n->getChildrenSize() == 3)
            return nonzero(n->getChild(1), false) && nonzero(n->getChild(2), false);
        return false;
    }
    std::optional<IntervalZ> interval(Node n, bool constantsOnly = false) {
        Nodes::Frame frame(nodes);
        if (!n || !n->getSort() || (!n->getSort()->isInt() && !n->getSort()->isIntOrReal()))
            return {};
        auto k = n->getKind();
        auto size = n->getChildrenSize();
        if (k == K::NT_CONST && !size) {
            const auto value = n->getValue();
            const auto text = value && value->getType() == SOMTParser::NUMBER
                                  ? value->getNumberValue().toString()
                                  : n->getName();
            nodes.budget.tick(text.size());
            auto rational = mpqFromString(text);
            if (rational.get_den() != 1)
                return {};
            return IntervalZ{rational.get_num(), rational.get_num()};
        }
        if (k == K::NT_VAR && n->getSort()->isInt() && !constantsOnly) {
            auto it = box.find(n);
            if (it != box.end() && it->second.lower && it->second.upper)
                return IntervalZ{*it->second.lower, *it->second.upper};
            return {};
        }
        if (k == K::NT_ITE && size == 3) {
            auto condition = boolean(n->getChild(0), constantsOnly);
            if (condition != Truth::Open)
                return interval(n->getChild(condition == Truth::Yes ? 1 : 2), constantsOnly);
            auto a = interval(n->getChild(1), constantsOnly);
            auto b = interval(n->getChild(2), constantsOnly);
            if (a && b)
                return IntervalZ{std::min(a->lo, b->lo), std::max(a->hi, b->hi)};
            return {};
        }
        if ((k == K::NT_NEG || k == K::NT_ABS) && size == 1) {
            auto a = interval(n->getChild(0), constantsOnly);
            if (!a)
                return {};
            if (k == K::NT_NEG)
                return intervalNeg(*a);
            const mpz_class lo = abs(a->lo), hi = abs(a->hi);
            return IntervalZ{a->containsZero() ? mpz_class(0) : std::min(lo, hi), std::max(lo, hi)};
        }
        if ((k != K::NT_ADD && k != K::NT_SUB && k != K::NT_MUL && k != K::NT_DIV_INT &&
             k != K::NT_MOD && k != K::NT_POW) ||
            size < 2)
            return {};
        if ((k == K::NT_DIV_INT || k == K::NT_MOD || k == K::NT_POW) && size != 2)
            return {};
        auto a = interval(n->getChild(0), constantsOnly);
        if (!a)
            return {};
        for (std::size_t i = 1; i < size; ++i) {
            auto b = interval(n->getChild(i), constantsOnly);
            if (!b)
                return {};
            nodes.budget.tick(
                mpz_sizeinbase(a->lo.get_mpz_t(), 2) + mpz_sizeinbase(a->hi.get_mpz_t(), 2) +
                mpz_sizeinbase(b->lo.get_mpz_t(), 2) + mpz_sizeinbase(b->hi.get_mpz_t(), 2));
            if (k == K::NT_ADD)
                a = intervalAdd(*a, *b);
            else if (k == K::NT_SUB)
                a = intervalSub(*a, *b);
            else if (k == K::NT_MUL)
                a = size == 2 && n->getChild(0) == n->getChild(1) ? intervalPow(*a, 2)
                                                                  : intervalMul(*a, *b);
            else if (k == K::NT_POW) {
                if (b->lo != b->hi || b->lo < 0 || !b->lo.fits_uint_p())
                    return {};
                auto exponent = static_cast<uint32_t>(b->lo.get_ui());
                auto bits = std::max(mpz_sizeinbase(a->lo.get_mpz_t(), 2),
                                     mpz_sizeinbase(a->hi.get_mpz_t(), 2));
                if (exponent && bits > SIZE_MAX / exponent)
                    throw ResourceExhausted("range power construction budget exhausted");
                nodes.budget.tick(bits * exponent);
                a = intervalPow(*a, exponent);
            } else {
                if (b->containsZero() && !nonzero(n->getChild(i), constantsOnly))
                    return {}; // SMT division by zero is not Rocq's totalization.
                if (k == K::NT_MOD) {
                    mpz_class maximum = std::max(mpz_class(abs(b->lo)), mpz_class(abs(b->hi)));
                    a = IntervalZ{0, maximum - 1};
                } else if (b->containsZero()) {
                    mpz_class maximum = std::max(mpz_class(abs(a->lo)), mpz_class(abs(a->hi)));
                    a = IntervalZ{-maximum, maximum};
                } else {
                    auto quotient = [](const mpz_class &x, const mpz_class &y) {
                        mpz_class q;
                        if (y > 0)
                            mpz_fdiv_q(q.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t());
                        else
                            mpz_cdiv_q(q.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t());
                        return q;
                    };
                    mpz_class values[]{quotient(a->lo, b->lo), quotient(a->lo, b->hi),
                                       quotient(a->hi, b->lo), quotient(a->hi, b->hi)};
                    a = IntervalZ{*std::min_element(values, values + 4),
                                  *std::max_element(values, values + 4)};
                }
            }
        }
        return a;
    }
    Truth boolean(Node n, bool constantsOnly = false) {
        Nodes::Frame frame(nodes);
        if (!n || !n->getSort() || !n->getSort()->isBool())
            return Truth::Open;
        if (!constantsOnly && assumptions.contains(n))
            return Truth::Yes;
        auto k = n->getKind();
        auto size = n->getChildrenSize();
        if (k == K::NT_CONST_TRUE)
            return Truth::Yes;
        if (k == K::NT_CONST_FALSE)
            return Truth::No;
        if (k == K::NT_NOT && size == 1)
            return invert(boolean(n->getChild(0), constantsOnly));
        if (k == K::NT_ITE && size == 3) {
            auto c = boolean(n->getChild(0), constantsOnly);
            if (c != Truth::Open)
                return boolean(n->getChild(c == Truth::Yes ? 1 : 2), constantsOnly);
            auto a = boolean(n->getChild(1), constantsOnly);
            return a == boolean(n->getChild(2), constantsOnly) ? a : Truth::Open;
        }
        if (k == K::NT_AND || k == K::NT_OR) {
            bool open = false;
            for (auto child : SOMTParser::children(n)) {
                auto t = boolean(child, constantsOnly);
                if (t == (k == K::NT_AND ? Truth::No : Truth::Yes))
                    return t;
                open |= t == Truth::Open;
            }
            return open ? Truth::Open : k == K::NT_AND ? Truth::Yes : Truth::No;
        }
        if (k == K::NT_IMPLIES && size >= 2) {
            bool open = false;
            for (std::size_t i = 0; i + 1 < size; ++i) {
                auto t = boolean(n->getChild(i), constantsOnly);
                if (t == Truth::No)
                    return Truth::Yes;
                open |= t == Truth::Open;
            }
            auto t = boolean(n->getChild(size - 1), constantsOnly);
            return t == Truth::Yes ? t : open ? Truth::Open : t;
        }
        if ((k != K::NT_LE && k != K::NT_LT && k != K::NT_GE && k != K::NT_GT && k != K::NT_EQ &&
             k != K::NT_DISTINCT) ||
            size != 2)
            return Truth::Open;
        if (k == K::NT_EQ || k == K::NT_DISTINCT)
            for (std::size_t i = 0; i < 2; ++i) {
                auto zero = interval(n->getChild(i), true);
                if (zero && zero->lo == 0 && zero->hi == 0 &&
                    nonzero(n->getChild(1 - i), constantsOnly))
                    return k == K::NT_EQ ? Truth::No : Truth::Yes;
            }
        auto a = interval(n->getChild(0), constantsOnly),
             b = interval(n->getChild(1), constantsOnly);
        if (!a || !b)
            return Truth::Open;
        bool yes, no;
        switch (k) {
        case K::NT_LE:
            yes = a->hi <= b->lo;
            no = a->lo > b->hi;
            break;
        case K::NT_LT:
            yes = a->hi < b->lo;
            no = a->lo >= b->hi;
            break;
        case K::NT_GE:
            yes = a->lo >= b->hi;
            no = a->hi < b->lo;
            break;
        case K::NT_GT:
            yes = a->lo > b->hi;
            no = a->hi <= b->lo;
            break;
        default:
            yes = a->lo == a->hi && b->lo == b->hi && a->lo == b->lo;
            no = a->hi < b->lo || b->hi < a->lo;
        }
        auto result = yes ? Truth::Yes : no ? Truth::No : Truth::Open;
        return k == K::NT_DISTINCT ? invert(result) : result;
    }
    std::optional<RangeBound> bound(Node premise) {
        Nodes::Frame frame(nodes);
        auto k = premise->getKind();
        if ((k != K::NT_LE && k != K::NT_LT && k != K::NT_GE && k != K::NT_GT && k != K::NT_EQ) ||
            premise->getChildrenSize() != 2)
            return {};
        for (bool reverse : {false, true}) {
            auto symbol = premise->getChild(reverse ? 1 : 0);
            auto value = interval(premise->getChild(reverse ? 0 : 1), true);
            if (symbol->getKind() != K::NT_VAR || !symbol->getSort() ||
                !symbol->getSort()->isInt() || !value || value->lo != value->hi)
                continue;
            RangeBound result;
            result.symbol = symbol;
            bool lower = k == K::NT_EQ || (reverse ? k == K::NT_LE || k == K::NT_LT
                                                   : k == K::NT_GE || k == K::NT_GT);
            bool upper = k == K::NT_EQ || !lower;
            const bool strict = k == K::NT_LT || k == K::NT_GT;
            if (lower) {
                result.lower = value->lo + (strict ? 1 : 0);
                result.lowerAssumption = premise;
            }
            if (upper) {
                result.upper = value->lo - (strict ? 1 : 0);
                result.upperAssumption = premise;
            }
            return result;
        }
        return {};
    }
    void discover() {
        for (auto a : assumptions)
            if (auto b = bound(a)) {
                auto &entry = box[b->symbol];
                entry.symbol = b->symbol;
                if (b->lower && (!entry.lower || *b->lower > *entry.lower)) {
                    entry.lower = b->lower;
                    entry.lowerAssumption = a;
                }
                if (b->upper && (!entry.upper || *b->upper < *entry.upper)) {
                    entry.upper = b->upper;
                    entry.upperAssumption = a;
                }
            }
    }
    bool proved(Node conclusion) {
        for (const auto &[_, b] : box)
            if (b.lower && b.upper && *b.lower > *b.upper)
                return true;
        for (auto a : assumptions)
            if (a->getKind() == K::NT_CONST_FALSE)
                return true;
        return boolean(conclusion) == Truth::Yes;
    }
    void replay(const RangeCertificate &certificate) {
        for (const auto &b : certificate.bounds) {
            nodes.budget.tick();
            if (!b.symbol || box.contains(b.symbol) || (!b.lower && !b.upper))
                throw std::invalid_argument("invalid or duplicate range certificate bound");
            for (bool lower : {false, true}) {
                const auto &endpoint = lower ? b.lower : b.upper;
                const auto &source = lower ? b.lowerAssumption : b.upperAssumption;
                if (!endpoint) {
                    if (source)
                        throw std::invalid_argument("range source without an endpoint");
                    continue;
                }
                if (!assumptions.contains(source))
                    throw std::invalid_argument("range premise is not a mandatory assumption");
                auto fact = bound(source);
                auto value = fact ? lower ? fact->lower : fact->upper : std::optional<mpz_class>{};
                if (!fact || fact->symbol != b.symbol || !value || *value != *endpoint)
                    throw std::invalid_argument("range certificate endpoint is not justified");
            }
            box.emplace(b.symbol, b);
        }
    }
};
} // namespace
RangeAnswer RangeSolver::solve(const Obligation &o) {
    RangeAnswer answer;
    try {
        Engine e(o, workLimit_);
        e.discover();
        if (e.proved(o.conclusion)) {
            answer.status = Status::Valid;
            RangeCertificate c;
            for (const auto &[_, b] : e.box)
                c.bounds.push_back(b);
            answer.certificate = std::move(c);
        } else
            answer.reason = "integer interval proof remains open";
        answer.work = e.nodes.budget.used();
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
RangeAnswer RangeCertificateSolver::solve(const RangeCertificateProblem &p) {
    RangeAnswer answer;
    try {
        Engine e(p.obligation, workLimit_);
        e.replay(p.certificate);
        answer.status = e.proved(p.obligation.conclusion) ? Status::Valid : Status::Invalid;
        answer.work = e.nodes.budget.used();
    } catch (const std::invalid_argument &e) {
        answer.status = Status::Invalid;
        answer.reason = e.what();
    } catch (const std::exception &e) {
        answer.reason = e.what();
    }
    return answer;
}
RangeAssistedAnswer RangeAssistedSolver::solve(const Obligation &o) {
    RangeAssistedAnswer answer;
    auto interval = RangeSolver(workLimit_).solve(o);
    answer.intervalWork = interval.work;
    if (interval.status == Status::InvalidInput) {
        answer.status = interval.status;
        answer.reason = interval.reason;
        return answer;
    }
    if (interval.status == Status::Valid && interval.certificate) {
        auto replay = RangeCertificateSolver(workLimit_).solve({o, *interval.certificate});
        answer.intervalWork += replay.work;
        if (replay.status == Status::Valid) {
            answer.status = Status::Valid;
            answer.method = VerificationMethod::Interval;
            answer.certificate = std::move(interval.certificate);
            return answer;
        }
    }
    static_cast<Answer &>(answer) = verification::Solver(decide_).solve({{o}});
    return answer;
}
} // namespace xolver::applications::sv::verification
