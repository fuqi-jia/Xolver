#include "xolver/Script.h"
#include <cctype>
#include <stdexcept>

namespace xolver {
namespace {
struct Command { std::string_view text; std::string name; size_t arguments; };
void skipSpace(std::string_view s, size_t& i) {
    while (i < s.size()) {
        if (std::isspace(static_cast<unsigned char>(s[i]))) { ++i; continue; }
        if (s[i] == ';') { while (i < s.size() && s[i] != '\n') ++i; continue; }
        break;
    }
}
std::vector<Command> commands(std::string_view s) {
    std::vector<Command> result;
    size_t i = 0;
    while (true) {
        skipSpace(s, i);
        if (i == s.size()) return result;
        const size_t begin = i;
        if (s[i++] != '(') throw std::invalid_argument("expected SMT-LIB command");
        skipSpace(s, i);
        const size_t nameBegin = i;
        while (i < s.size() && !std::isspace(static_cast<unsigned char>(s[i])) &&
               s[i] != '(' && s[i] != ')' && s[i] != ';') ++i;
        std::string name(s.substr(nameBegin, i - nameBegin));
        const size_t arguments = i - begin;
        int depth = 1;
        bool quoted = false, symbol = false, comment = false;
        for (; i < s.size() && depth; ++i) {
            const char c = s[i];
            if (comment) { if (c == '\n') comment = false; continue; }
            if (symbol) { if (c == '|') symbol = false; continue; }
            if (quoted) {
                if (c == '"') {
                    if (i + 1 < s.size() && s[i + 1] == '"') ++i;
                    else quoted = false;
                }
                continue;
            }
            if (c == ';') comment = true;
            else if (c == '"') quoted = true;
            else if (c == '|') symbol = true;
            else if (c == '(') ++depth;
            else if (c == ')') --depth;
        }
        if (depth || quoted || symbol) throw std::invalid_argument("unterminated SMT-LIB command");
        result.push_back({s.substr(begin, i - begin), std::move(name), arguments});
        if (result.back().name == "exit") return result;
    }
}
bool response(const std::string& n) {
    return n == "echo" || n.rfind("get-", 0) == 0;
}
std::string query(const Command& c) {
    if (c.name == "check-sat") return std::string(c.text) + "\n";
    size_t i = c.arguments;
    skipSpace(c.text, i);
    // The command scanner checked balance. The sole argument must be a list.
    if (i >= c.text.size() || c.text[i] != '(')
        throw std::invalid_argument("check-sat-assuming requires an assumption list");
    size_t end = i + 1;
    int depth = 1;
    bool quoted = false, symbol = false, comment = false;
    for (; end < c.text.size() && depth; ++end) {
        const char ch = c.text[end];
        if (comment) { if (ch == '\n') comment = false; continue; }
        if (symbol) { if (ch == '|') symbol = false; continue; }
        if (quoted) {
            if (ch == '"') {
                if (end + 1 < c.text.size() && c.text[end + 1] == '"') ++end;
                else quoted = false;
            }
            continue;
        }
        if (ch == ';') comment = true;
        else if (ch == '|') symbol = true;
        else if (ch == '"') quoted = true;
        else if (ch == '(') ++depth;
        else if (ch == ')') --depth;
    }
    size_t tail = end;
    skipSpace(c.text, tail);
    if (depth || tail != c.text.size() - 1 || c.text[tail] != ')')
        throw std::invalid_argument("invalid check-sat-assuming list");
    // Build a valid standalone query instead of relying on the pinned parser's
    // broken check-sat-assuming closing-parenthesis consumption. The asserted
    // assumptions occur only in this snapshot, never in the persistent prefix.
    return "(assert (and " + std::string(c.text.substr(i + 1, end - i - 2)) +
           "\n))\n(check-sat)\n";
}
}
std::vector<std::string> smtQuerySnapshots(std::string_view source) {
    std::vector<std::string> snapshots;
    std::string prefix, beforeFirstQuery;
    bool changedSinceQuery = false;
    for (const auto& c : commands(source)) {
        if (c.name == "check-sat" || c.name == "check-sat-assuming") {
            snapshots.push_back(prefix + beforeFirstQuery + query(c));
            beforeFirstQuery.clear();
            changedSinceQuery = false;
        } else if (response(c.name) || c.name == "exit") {
            if (changedSinceQuery && c.name != "echo" && c.name != "get-info" &&
                c.name != "get-option" && c.name != "get-assertions" && c.name != "exit")
                throw std::invalid_argument("model/proof response requested after context changed");
            auto& dst = snapshots.empty() ? beforeFirstQuery : snapshots.back();
            dst += c.text;
            dst += '\n';
        } else {
            prefix += c.text;
            prefix += '\n';
            // Metadata cannot invalidate a previously computed model.
            if (!snapshots.empty() && c.name != "set-info") changedSinceQuery = true;
        }
    }
    if (snapshots.empty()) snapshots.push_back(prefix + beforeFirstQuery);
    return snapshots;
}
}
