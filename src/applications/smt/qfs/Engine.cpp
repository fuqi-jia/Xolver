#include "applications/smt/qfs/Engine.h"
#include "applications/smt/lia/Solver.h"
#include "base/MpqUtils.h"
#include "ir/NativeBuilder.h"
#include <functional>
#include <map>
#include <sstream>

namespace xolver::applications::smt::strings {
namespace {
using namespace xolver::native;
using Text = std::u32string;
Text decode(const std::string &text) {
    if (text.size() < 2 || text.front() != '"' || text.back() != '"')
        throw Unsupported("invalid SMT string literal");
    Text out;
    for (std::size_t i = 1; i + 1 < text.size(); ++i) {
        unsigned char c = text[i];
        if (c == '"') {
            if (i + 2 >= text.size() || text[++i] != '"')
                throw Unsupported("invalid string quote");
            out.push_back('"');
        } else if (c == '\\' && i + 2 < text.size() && text[i + 1] == 'u') {
            const auto start = i;
            i += 2;
            bool braced = text[i] == '{';
            if (braced)
                ++i;
            std::size_t digits = 0;
            char32_t value = 0;
            while (i + 1 < text.size() && (braced ? text[i] != '}' : digits < 4)) {
                const auto h = text[i];
                unsigned d = h >= '0' && h <= '9'   ? h - '0'
                             : h >= 'a' && h <= 'f' ? h - 'a' + 10
                             : h >= 'A' && h <= 'F' ? h - 'A' + 10
                                                    : 16;
                if (d == 16 || digits == 5)
                    break;
                value = value * 16 + d;
                ++digits;
                ++i;
            }
            if ((braced && digits > 0 && i + 1 < text.size() && text[i] == '}') ||
                (!braced && digits == 4)) {
                if (value > 0x2ffff)
                    throw Unsupported("Unicode code point outside SMT-LIB alphabet");
                out.push_back(value);
                if (!braced)
                    --i;
            } else {
                i = start;
                out.push_back('\\');
            }
        } else if (c >= 0x80) {
            // SOMTParser normalizes escaped code points to UTF-8 in native
            // constant names. Validate and decode that representation exactly.
            const unsigned width = c >= 0xc2 && c <= 0xdf   ? 2
                                   : c >= 0xe0 && c <= 0xef ? 3
                                   : c >= 0xf0 && c <= 0xf4 ? 4
                                                            : 0;
            if (!width || i + width >= text.size())
                throw Unsupported("invalid UTF-8 string constant");
            char32_t value = c & (0x7f >> width);
            for (unsigned j = 1; j < width; ++j) {
                const auto next = static_cast<unsigned char>(text[i + j]);
                if ((next & 0xc0) != 0x80)
                    throw Unsupported("invalid UTF-8 continuation");
                value = (value << 6) | (next & 0x3f);
            }
            const char32_t minimum = width == 2 ? 0x80 : width == 3 ? 0x800 : 0x10000;
            if (value < minimum || value > 0x2ffff)
                throw Unsupported("code point outside SMT-LIB string alphabet");
            out.push_back(value);
            i += width - 1;
        } else if (c >= 0x20 && c <= 0x7f)
            out.push_back(c);
        else
            throw Unsupported("use SMT-LIB Unicode escapes in string literals");
    }
    return out;
}
std::string encode(const Text &text) {
    std::ostringstream out;
    out << '"';
    for (auto c : text) {
        if (c == '"')
            out << "\"\"";
        else if (c >= 0x20 && c <= 0x7e && c != '\\')
            out << char(c);
        else
            out << "\\u{" << std::hex << unsigned(c) << '}';
    }
    out << '"';
    return out.str();
}
class Engine {
    Nodes b;
    NativeAssertions roots, atoms;
    std::vector<Node> vars;
    std::map<Node, Text> assignment, forced;
    std::set<Text> literals;
    std::map<Node, Node> cache;
    bool equalityOnly = true;
    static bool stringSort(Node n) { return n && n->getSort() && n->getSort()->isStr(); }
    Node text(const Text &v) {
        b.budget.tick(v.size());
        return b.make(SOMTParser::SortManager::getStr(), K::NT_CONST, {}, encode(v));
    }
    Node integer(const mpz_class &v) {
        return b.make(SOMTParser::SortManager::getInt(), K::NT_CONST, {}, v.get_str());
    }
    Text asText(Node n) {
        n = fold(n);
        if (n->getKind() != K::NT_CONST || !stringSort(n))
            throw Unsupported("unbound string value");
        return decode(n->getName());
    }
    mpz_class asInt(Node n) {
        n = fold(n);
        if (n->getKind() != K::NT_CONST)
            throw Unsupported("string index requires a concrete integer");
        auto q = mpqFromString(n->getName());
        if (q.get_den() != 1)
            throw Unsupported("non-integer string index");
        return q.get_num();
    }
    bool matches(Node regex, const Text &value) {
        std::map<std::tuple<Node, std::size_t, std::size_t>, bool> memo;
        std::function<bool(Node, std::size_t, std::size_t)> test = [&](Node r, std::size_t first,
                                                                       std::size_t last) -> bool {
            Nodes::Frame frame(b);
            b.budget.tick();
            const auto key = std::tuple{r, first, last};
            if (auto it = memo.find(key); it != memo.end())
                return it->second;
            bool result = false;
            const auto k = r->getKind();
            const auto count = r->getChildrenSize();
            if (k == K::NT_REG_NONE)
                result = false;
            else if (k == K::NT_REG_ALL)
                result = true;
            else if (k == K::NT_REG_ALLCHAR)
                result = last - first == 1;
            else if (k == K::NT_STR_TO_REG && count == 1)
                result = value.substr(first, last - first) == asText(r->getChild(0));
            else if (k == K::NT_REG_RANGE && count == 2) {
                const auto lo = asText(r->getChild(0)), hi = asText(r->getChild(1));
                result = lo.size() == 1 && hi.size() == 1 && last - first == 1 &&
                         lo[0] <= value[first] && value[first] <= hi[0];
            } else if (k == K::NT_REG_UNION || k == K::NT_REG_INTER || k == K::NT_REG_DIFF ||
                       k == K::NT_REG_COMPLEMENT) {
                if ((k == K::NT_REG_COMPLEMENT && count != 1) ||
                    (k == K::NT_REG_DIFF && count != 2))
                    throw Unsupported("regex arity");
                result = k == K::NT_REG_INTER;
                for (std::size_t i = 0; i < count; ++i) {
                    const auto child = test(r->getChild(i), first, last);
                    if (k == K::NT_REG_UNION)
                        result |= child;
                    else if (k == K::NT_REG_INTER)
                        result &= child;
                    else if (k == K::NT_REG_COMPLEMENT)
                        result = !child;
                    else
                        result = i ? result && !child : child;
                }
            } else if (k == K::NT_REG_CONCAT) {
                std::set<std::size_t> reached{first};
                for (auto child : SOMTParser::children(r)) {
                    std::set<std::size_t> next;
                    for (auto i : reached)
                        for (auto j = i; j <= last; ++j)
                            if (test(child, i, j))
                                next.insert(j);
                    reached = std::move(next);
                }
                result = reached.contains(last);
            } else if (k == K::NT_REG_STAR || k == K::NT_REG_PLUS || k == K::NT_REG_OPT) {
                if (count != 1)
                    throw Unsupported("regex repetition arity");
                auto child = r->getChild(0);
                if (k == K::NT_REG_OPT)
                    result = first == last || test(child, first, last);
                else {
                    std::vector<bool> reached(last - first + 1, false);
                    reached[0] = true;
                    for (auto i = first; i < last; ++i)
                        if (reached[i - first])
                            for (auto j = i + 1; j <= last; ++j)
                                if (test(child, i, j))
                                    reached[j - first] = true;
                    result = reached.back() &&
                             (k == K::NT_REG_STAR || first != last || test(child, first, last));
                }
            } else
                throw Unsupported("regular-expression operator backend unavailable");
            memo[key] = result;
            return result;
        };
        return test(regex, 0, value.size());
    }
    Node fold(Node n) {
        Nodes::Frame frame(b);
        b.budget.tick();
        if (!n || !n->getSort())
            throw Unsupported("null string term");
        if (auto it = cache.find(n); it != cache.end())
            return it->second;
        const auto k = n->getKind();
        const auto count = n->getChildrenSize();
        Node out;
        if (k == K::NT_FORALL || k == K::NT_EXISTS || k == K::NT_UF_APPLY || k == K::NT_FUNC_APPLY)
            throw Unsupported("string binder/UF backend unavailable");
        if (k == K::NT_VAR && stringSort(n)) {
            auto it = assignment.find(n);
            if (it == assignment.end())
                throw Unsupported("unbound string value");
            out = text(it->second);
        } else if (k == K::NT_LET || k == K::NT_LET_CHAIN || k == K::NT_LET_BIND_VAR) {
            if (!count)
                throw Unsupported("empty let");
            out = fold(n->getChild(k == K::NT_LET_CHAIN ? count - 1 : 0));
        } else if (k == K::NT_CONST && stringSort(n))
            out = text(decode(n->getName()));
        else if (k == K::NT_STR_IN_REG) {
            if (count != 2)
                throw Unsupported("regex membership arity");
            out = b.boolean(matches(n->getChild(1), asText(n->getChild(0))));
        } else if (k == K::NT_STR_FROM_INT || k == K::NT_STR_FROM_CODE) {
            if (count != 1)
                throw Unsupported("string conversion arity");
            const auto v = asInt(n->getChild(0));
            Text s;
            if (k == K::NT_STR_FROM_INT && v >= 0) {
                const auto dec = v.get_str();
                s.assign(dec.begin(), dec.end());
            }
            if (k == K::NT_STR_FROM_CODE && v >= 0 && v <= 0x2ffff)
                s.push_back(v.get_ui());
            out = text(s);
        } else if (k >= K::NT_STR_LEN && k <= K::NT_STR_TO_CODE) {
            if (!count)
                throw Unsupported("string operator arity");
            const auto a = asText(n->getChild(0));
            if (k == K::NT_STR_CONCAT) {
                Text s = a;
                for (std::size_t i = 1; i < count; ++i) {
                    auto part = asText(n->getChild(i));
                    b.budget.tick(part.size());
                    s += part;
                }
                out = text(s);
            } else if (k == K::NT_STR_LEN && count == 1)
                out = integer(mpz_class(a.size()));
            else if (k == K::NT_STR_TO_CODE && count == 1)
                out = integer(a.size() == 1 ? mpz_class(unsigned(a[0])) : mpz_class(-1));
            else if (k == K::NT_STR_TO_INT && count == 1) {
                mpz_class v = 0;
                if (a.empty())
                    v = -1;
                for (auto c : a) {
                    b.budget.tick();
                    if (c < '0' || c > '9') {
                        v = -1;
                        break;
                    }
                    v = v * 10 + unsigned(c - '0');
                }
                out = integer(v);
            } else if ((k == K::NT_STR_CHARAT && count == 2) ||
                       (k == K::NT_STR_SUBSTR && count == 3)) {
                const auto start = asInt(n->getChild(1));
                const auto len = k == K::NT_STR_CHARAT ? mpz_class(1) : asInt(n->getChild(2));
                if (start < 0 || len <= 0 || start >= mpz_class(a.size()))
                    out = text({});
                else {
                    const auto begin = start.get_ui();
                    const mpz_class remaining = a.size() - begin;
                    out = text(a.substr(begin, len >= remaining ? a.size() - begin : len.get_ui()));
                }
            } else if (count >= 2) {
                const auto c = asText(n->getChild(1));
                if (k == K::NT_STR_CONTAINS && count == 2)
                    out = b.boolean(a.find(c) != Text::npos);
                else if (k == K::NT_STR_PREFIXOF && count == 2)
                    out = b.boolean(c.starts_with(a));
                else if (k == K::NT_STR_SUFFIXOF && count == 2)
                    out = b.boolean(c.ends_with(a));
                else if (k == K::NT_STR_LT && count == 2)
                    out = b.boolean(a < c);
                else if (k == K::NT_STR_LE && count == 2)
                    out = b.boolean(a <= c);
                else if (k == K::NT_STR_INDEXOF && count == 3) {
                    auto from = asInt(n->getChild(2));
                    const auto at = from < 0 || from > mpz_class(a.size())
                                        ? Text::npos
                                        : a.find(c, from.get_ui());
                    out = integer(at == Text::npos ? mpz_class(-1) : mpz_class(at));
                } else if ((k == K::NT_STR_REPLACE || k == K::NT_STR_REPLACE_ALL) && count == 3) {
                    auto replacement = asText(n->getChild(2));
                    Text s = a;
                    if (k == K::NT_STR_REPLACE) {
                        const auto at = s.find(c);
                        if (at != Text::npos)
                            s.replace(at, c.size(), replacement);
                    } else if (!c.empty()) {
                        std::size_t at = 0;
                        while ((at = s.find(c, at)) != Text::npos) {
                            b.budget.tick(replacement.size() + 1);
                            s.replace(at, c.size(), replacement);
                            at += replacement.size();
                        }
                    }
                    out = text(s);
                }
            }
            if (!out)
                throw Unsupported("string operator backend unavailable");
        } else if ((k == K::NT_EQ || k == K::NT_EQ_OTHER || k == K::NT_DISTINCT ||
                    k == K::NT_DISTINCT_OTHER) &&
                   count >= 2 && stringSort(n->getChild(0))) {
            bool equal = true;
            const bool distinct = k == K::NT_DISTINCT || k == K::NT_DISTINCT_OTHER;
            std::vector<Text> words;
            for (auto c : SOMTParser::children(n))
                words.push_back(asText(c));
            for (std::size_t i = 0; i < count; ++i)
                for (std::size_t j = i + 1; j < count; ++j)
                    if (distinct || i == 0)
                        equal &= distinct ? words[i] != words[j] : words[i] == words[j];
            out = b.boolean(equal);
        } else if (k == K::NT_ITE && stringSort(n))
            throw Unsupported("symbolic string ite requires word-equation backend");
        else {
            std::vector<Node> args;
            for (auto c : SOMTParser::children(n))
                args.push_back(fold(c));
            out = b.make(n->getSort(), k, args, n->getName());
        }
        cache[n] = out;
        return out;
    }

  public:
    Engine(const NativeAssertions &input, std::size_t work) : b(input, work), roots(input) {
        std::vector<Node> pending = roots;
        std::set<Node> seen;
        std::set<std::string> names;
        while (!pending.empty()) {
            auto n = pending.back();
            pending.pop_back();
            if (!n || !seen.insert(n).second)
                continue;
            b.budget.tick();
            if (n->getKind() == K::NT_VAR && stringSort(n)) {
                if (!names.insert(n->getName()).second)
                    throw Unsupported("ambiguous string variable");
                vars.push_back(n);
            }
            if (n->getKind() == K::NT_CONST && stringSort(n))
                literals.insert(decode(n->getName()));
            if (n->getKind() >= K::NT_STR_LEN && n->getKind() <= K::NT_STR_FROM_CODE)
                equalityOnly = false;
            for (auto c : SOMTParser::children(n))
                pending.push_back(c);
        }
        pending = roots;
        while (!pending.empty()) {
            auto n = pending.back();
            pending.pop_back();
            if (n->getKind() == K::NT_AND)
                for (auto c : SOMTParser::children(n))
                    pending.push_back(c);
            else
                atoms.push_back(n);
        }
    }
    SolverAnswer solve(quantifiers::Limits limits) {
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto n : atoms)
                if ((n->getKind() == K::NT_EQ || n->getKind() == K::NT_EQ_OTHER) &&
                    n->getChildrenSize() == 2)
                    for (int side = 0; side < 2; ++side) {
                        auto v = n->getChild(side);
                        if (v->getKind() != K::NT_VAR || !stringSort(v))
                            continue;
                        try {
                            cache.clear();
                            auto value = asText(n->getChild(1 - side));
                            auto [it, inserted] = assignment.emplace(v, value);
                            if (!inserted && it->second != value) {
                                SolverAnswer a;
                                a.result = Result::Unsat;
                                return a;
                            }
                            changed |= inserted;
                        } catch (const Unsupported &) {
                        }
                    }
        }
        forced = assignment;
        auto candidates = literals;
        candidates.insert({});
        candidates.insert(U"a");
        for (std::size_t i = 0, added = 0; added < vars.size(); ++i) {
            auto s = std::string("@") + std::to_string(i);
            if (candidates.insert(Text(s.begin(), s.end())).second)
                ++added;
        }
        std::vector<Node> unbound;
        for (auto v : vars)
            if (!assignment.contains(v))
                unbound.push_back(v);
        bool anyUnknown = false;
        SolverAnswer answer;
        std::string reason;
        std::function<bool(std::size_t)> search = [&](std::size_t i) {
            Nodes::Frame frame(b);
            b.budget.tick();
            if (i < unbound.size()) {
                for (const auto &candidate : candidates) {
                    assignment[unbound[i]] = candidate;
                    if (search(i + 1))
                        return true;
                }
                return false;
            }
            cache.clear();
            NativeAssertions reduced;
            try {
                for (auto root : roots)
                    reduced.push_back(fold(root));
            } catch (const Unsupported &e) {
                anyUnknown = true;
                reason = e.what();
                return false;
            }
            pa::Limits integerLimits;
            integerLimits.work = limits.work;
            auto r = lia::solve(reduced, integerLimits, {});
            if (r.result == Result::Unknown) {
                anyUnknown = true;
                reason = r.reason;
                return false;
            }
            if (r.result != Result::Sat)
                return false;
            if (!r.model)
                r.model.emplace();
            for (const auto &[v, s] : assignment)
                r.model->assignments[v->getName()] = "#smt:" + encode(s);
            answer = std::move(r);
            return true;
        };
        if (search(0))
            return answer;
        if (!anyUnknown && (unbound.empty() || equalityOnly))
            answer.result = Result::Unsat;
        else
            answer.reason =
                anyUnknown ? reason
                           : "unbounded string search requires an additional word-equation backend";
        return answer;
    }
};
} // namespace
SolverAnswer solve(const NativeAssertions &roots, quantifiers::Limits limits) {
    try {
        return Engine(roots, limits.work).solve(limits);
    } catch (const Unsupported &e) {
        SolverAnswer a;
        a.reason = e.what();
        return a;
    } catch (const ResourceExhausted &e) {
        SolverAnswer a;
        a.reason = e.what();
        return a;
    } catch (const std::invalid_argument &e) {
        SolverAnswer a;
        a.reason = e.what();
        return a;
    } catch (const std::bad_alloc &) {
        SolverAnswer a;
        a.reason = "string memory exhausted";
        return a;
    }
}
} // namespace xolver::applications::smt::strings
