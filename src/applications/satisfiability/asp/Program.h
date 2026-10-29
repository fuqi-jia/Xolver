#pragma once

#include <cstdint>
#include <gmpxx.h>
#include <istream>
#include <string>
#include <vector>

namespace xolver::applications::satisfiability::asp {

using Atom = std::uint32_t;
using Literal = std::int32_t; // Positive atom or default-negated negative atom.
struct WeightedLiteral {
    Literal literal = 0;
    mpz_class weight = 1;
};
struct Rule {
    // False: normal rule (zero or one head). True: independent head choices.
    bool choice = false;
    std::vector<Atom> head;
    // A normal body is a conjunction. A weighted body tests sum >= lowerBound.
    bool weighted = false;
    mpz_class lowerBound = 0;
    std::vector<WeightedLiteral> body;
};
struct Objective {
    std::int64_t priority = 0;
    // ASPIF terms are additive. Source-language tuple deduplication belongs to
    // the grounder and must not be replaced by literal-only deduplication.
    std::vector<WeightedLiteral> terms;
};
struct Output {
    std::string text;
    std::vector<Literal> condition;
};
struct Program {
    std::vector<Rule> rules;
    std::vector<Objective> objectives;
    std::vector<Output> output;
    std::vector<Literal> assumptions;
};
struct ParseResult {
    enum class Status { Parsed, InvalidInput, Unsupported } status = Status::InvalidInput;
    Program program;
    std::string reason;
};
// One initial ASPIF 1.0 step (including incremental-marked headers):
// normal/choice rules, monotone weighted bodies,
// minimization, output, projection and assumptions. Unsupported semantic
// directives and disjunctive heads are rejected explicitly.
ParseResult parseAspif(std::istream&, std::size_t maxBytes = 64 * 1024 * 1024);

} // namespace xolver::applications::satisfiability::asp
