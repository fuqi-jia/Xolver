#include "proof/AletheProof.h"

#include <sstream>

namespace xolver {
namespace proof {

std::string AletheProof::assume(const std::string& term) {
    Command c;
    c.id = "h" + std::to_string(++assumeCount_);
    c.isAssume = true;
    c.assumeTerm = term;
    commands_.push_back(std::move(c));
    return commands_.back().id;
}

std::string AletheProof::step(const std::vector<std::string>& clause,
                              const std::string& rule,
                              const std::vector<std::string>& premises,
                              const std::vector<std::string>& args) {
    Command c;
    c.id = "t" + std::to_string(++stepCount_);
    c.clause = clause;
    c.rule = rule;
    c.premises = premises;
    c.args = args;
    commands_.push_back(std::move(c));
    return commands_.back().id;
}

std::string AletheProof::serialize() const {
    std::ostringstream out;
    for (const auto& c : commands_) {
        if (c.isAssume) {
            out << "(assume " << c.id << ' ' << c.assumeTerm << ")\n";
            continue;
        }
        out << "(step " << c.id << " (cl";
        for (const auto& lit : c.clause) out << ' ' << lit;
        out << ") :rule " << c.rule;
        if (!c.premises.empty()) {
            out << " :premises (";
            for (size_t i = 0; i < c.premises.size(); ++i)
                out << (i ? " " : "") << c.premises[i];
            out << ")";
        }
        if (!c.args.empty()) {
            out << " :args (";
            for (size_t i = 0; i < c.args.size(); ++i)
                out << (i ? " " : "") << c.args[i];
            out << ")";
        }
        out << ")\n";
    }
    return out.str();
}

AletheProof buildConflictRefutation(const std::vector<AssertedLit>& lits,
                                    const std::string& rule,
                                    const std::vector<std::string>& args) {
    AletheProof p;
    std::vector<std::string> assumeIds;
    assumeIds.reserve(lits.size());
    for (const auto& l : lits)
        assumeIds.push_back(p.assume(l.positive ? l.atom : "(not " + l.atom + ")"));

    // The theory tautology (cl ¬L1 ... ¬Ln): negate each asserted literal, with
    // double negation simplified (positive -> (not atom), negative -> atom).
    std::vector<std::string> negClause;
    negClause.reserve(lits.size());
    for (const auto& l : lits)
        negClause.push_back(l.positive ? "(not " + l.atom + ")" : l.atom);
    std::string tautId = p.step(negClause, rule, /*premises=*/{}, args);

    // Resolve the tautology with the assumed atoms -> empty clause.
    std::vector<std::string> resPremises;
    resPremises.reserve(lits.size() + 1);
    resPremises.push_back(tautId);
    for (const auto& id : assumeIds) resPremises.push_back(id);
    p.step(/*clause=*/{}, "resolution", resPremises);
    return p;
}

} // namespace proof
} // namespace xolver
