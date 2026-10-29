#include "applications/satisfiability/asp/Program.h"
#include <charconv>
#include <limits>
#include <sstream>
#include <stdexcept>

namespace xolver::applications::satisfiability::asp {
namespace {
struct Unsupported : std::runtime_error { using std::runtime_error::runtime_error; };
class Line {
    std::istringstream input_;
public:
    explicit Line(const std::string& text) : input_(text) {}
    std::int64_t integer() {
        std::string token;
        if (!(input_ >> token)) throw std::invalid_argument("missing ASPIF integer");
        std::int64_t result = 0;
        const auto parsed = std::from_chars(token.data(), token.data()+token.size(), result);
        if (parsed.ec != std::errc{} || parsed.ptr != token.data()+token.size())
            throw std::invalid_argument("invalid ASPIF integer");
        return result;
    }
    std::size_t count() {
        const auto value = integer();
        if (value < 0 || value > 64000000) throw std::invalid_argument("invalid ASPIF list length");
        return static_cast<std::size_t>(value);
    }
    Literal literal() {
        const auto value = integer();
        if (!value || value <= std::numeric_limits<Literal>::min() || value > std::numeric_limits<Literal>::max())
            throw std::invalid_argument("invalid ASPIF literal");
        return static_cast<Literal>(value);
    }
    Atom atom() {
        const auto value = literal();
        if (value < 0) throw std::invalid_argument("ASPIF head atom must be positive");
        return static_cast<Atom>(value);
    }
    std::vector<Literal> literals() {
        std::vector<Literal> result;
        for (std::size_t n = count(); n; --n) result.push_back(literal());
        return result;
    }
    std::vector<WeightedLiteral> weighted(bool positive) {
        std::vector<WeightedLiteral> result;
        for (std::size_t n = count(); n; --n) {
            const auto lit = literal();
            const auto weight = integer();
            if (positive && weight < 0) throw Unsupported("negative weight in ASP rule body");
            result.push_back({lit, mpz_class(std::to_string(weight))});
        }
        return result;
    }
    std::string text() {
        const auto n = count();
        const auto separator = input_.get();
        if (separator != ' ') throw std::invalid_argument("missing ASPIF string separator");
        const auto available = input_.rdbuf()->in_avail();
        if (available < 0 || n > static_cast<std::size_t>(available))
            throw std::invalid_argument("truncated ASPIF output string");
        std::string value(n, '\0');
        if (n && !input_.read(value.data(), static_cast<std::streamsize>(n)))
            throw std::invalid_argument("truncated ASPIF output string");
        return value;
    }
    void end() {
        input_ >> std::ws;
        if (!input_.eof()) throw std::invalid_argument("extra ASPIF statement fields");
    }
};
}

ParseResult parseAspif(std::istream& input, std::size_t maxBytes) {
    ParseResult result;
    try {
        std::string text;
        std::size_t consumed = 0;
        auto line = [&] {
            if (!std::getline(input, text)) return false;
            if (text.size() > maxBytes || consumed > maxBytes-text.size())
                throw std::length_error("ASPIF input exceeds byte budget");
            consumed += text.size() + (input.eof() ? 0 : 1);
            if (consumed > maxBytes) throw std::length_error("ASPIF input exceeds byte budget");
            if (!text.empty() && text.back() == '\r') text.pop_back();
            return true;
        };
        if (!line()) throw std::invalid_argument("missing ASPIF header");
        std::istringstream header(text);
        std::string magic, extra;
        unsigned major = 0, minor = 0, revision = 0;
        if (!(header >> magic >> major >> minor >> revision) || magic != "asp")
            throw std::invalid_argument("invalid ASPIF header");
        if (major != 1 || minor != 0 || revision != 0)
            throw Unsupported("unsupported ASPIF version");
        if (header >> extra) throw Unsupported("incremental ASPIF is not supported");
        bool terminated = false;
        while (line()) {
            if (text.find_first_not_of(" \t\r") == std::string::npos) continue;
            Line fields(text);
            const auto directive = fields.integer();
            if (!directive) { fields.end(); terminated = true; break; }
            if (directive == 10) continue; // Comment has no semantics.
            if (directive == 1) {
                Rule rule;
                const auto kind = fields.integer();
                if (kind != 0 && kind != 1) throw std::invalid_argument("invalid ASPIF head type");
                rule.choice = kind == 1;
                for (std::size_t n = fields.count(); n; --n) rule.head.push_back(fields.atom());
                if (!rule.choice && rule.head.size() > 1)
                    throw Unsupported("disjunctive ASP rules are not supported");
                const auto body = fields.integer();
                if (body == 0) {
                    for (const auto lit : fields.literals()) rule.body.push_back({lit, 1});
                } else if (body == 1) {
                    rule.weighted = true;
                    rule.lowerBound = mpz_class(std::to_string(fields.integer()));
                    rule.body = fields.weighted(true);
                } else throw std::invalid_argument("invalid ASPIF body type");
                result.program.rules.push_back(std::move(rule));
            } else if (directive == 2) {
                Objective objective;
                objective.priority = fields.integer();
                objective.terms = fields.weighted(false);
                result.program.objectives.push_back(std::move(objective));
            } else if (directive == 3) {
                for (std::size_t n = fields.count(); n; --n) (void)fields.atom();
            } else if (directive == 4) {
                auto label = fields.text();
                auto condition = fields.literals();
                result.program.output.push_back({std::move(label), std::move(condition)});
            } else if (directive == 6) {
                const auto assumptions = fields.literals();
                result.program.assumptions.insert(result.program.assumptions.end(), assumptions.begin(), assumptions.end());
            } else throw Unsupported("unsupported ASPIF directive " + std::to_string(directive));
            fields.end();
        }
        if (!terminated) throw std::invalid_argument("missing ASPIF step terminator");
        while (line())
            if (text.find_first_not_of(" \t\r") != std::string::npos)
                throw Unsupported("multiple ASPIF steps are not supported");
        result.status = ParseResult::Status::Parsed;
    } catch (const Unsupported& error) {
        result.status = ParseResult::Status::Unsupported;
        result.reason = error.what();
    } catch (const std::exception& error) {
        result.reason = error.what();
    }
    return result;
}

} // namespace xolver::applications::satisfiability::asp
