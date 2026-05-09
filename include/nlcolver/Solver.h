#pragma once

#include "nlcolver/Result.h"
#include "nlcolver/Term.h"
#include "nlcolver/Sort.h"
#include "nlcolver/Model.h"
#include "nlcolver/Proof.h"
#include "nlcolver/Statistics.h"
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

namespace nlcolver {

/**
 * Value type for solver options.
 */
struct OptionValue {
    enum Kind { Bool, Int, Double, String } kind;
    union {
        bool b;
        int64_t i;
        double d;
    };
    std::string s;

    OptionValue(bool v) : kind(Bool), b(v) {}
    OptionValue(int64_t v) : kind(Int), i(v) {}
    OptionValue(double v) : kind(Double), d(v) {}
    OptionValue() = default; // required for unordered_map default construction
    OptionValue(std::string_view v) : kind(String), s(v) {}
};

/**
 * User-facing solver API.
 *
 * Design follows plan.md §1.1: Z3/cvc5-style, but minimal.
 */
class Solver {
public:
    Solver();
    ~Solver();

    // Non-copyable
    Solver(const Solver&) = delete;
    Solver& operator=(const Solver&) = delete;

    // Context
    void reset();
    void push();
    void pop(uint32_t n = 1);

    // Options
    void setLogic(std::string_view logic);
    void setOption(std::string_view key, OptionValue value);
    OptionValue getOption(std::string_view key) const;

    // Sorts
    Sort boolSort();
    Sort intSort();
    Sort realSort();
    Sort bvSort(uint32_t width);
    Sort fpSort(uint32_t ebits, uint32_t sbits);

    // Terms
    Term mkConst(Sort s, std::string_view name);
    Term mkVar(Sort s, std::string_view name);
    Term mkBool(bool v);
    Term mkInt(int64_t v);
    Term mkReal(const std::string& rational); // "1/3"
    Term mkOp(uint32_t kind, std::vector<Term> args);

    // Parsing
    bool parseFile(std::string_view filename);

    // Assertions
    void assertFormula(Term f);
    Result checkSat();
    Result checkSatAssuming(std::vector<Term> assumptions);

    // Results
    Model getModel() const;
    Term getValue(Term t) const;
    std::vector<Term> getUnsatCore() const;
    Proof getProof() const;
    Statistics getStatistics() const;

    // Debug / research
    void dumpSMT2(std::ostream& os);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace nlcolver
