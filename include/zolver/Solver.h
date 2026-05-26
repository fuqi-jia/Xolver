#pragma once

#include "zolver/Result.h"
#include "zolver/Term.h"
#include "zolver/Sort.h"
#include "zolver/Model.h"
#include "zolver/Proof.h"
#include "zolver/Statistics.h"
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <string_view>
#include <vector>

namespace zolver {

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
    Term getValue(Term t);
    std::vector<Term> getUnsatCore() const;
    Proof getProof() const;
    Statistics getStatistics() const;

    // SMT-COMP Model-Validation track: true iff the parsed input contained
    // a (get-model) command. After a `sat` result on such input, print the
    // model with dumpModel.
    bool modelRequested() const;
    // Write the model as an SMT-LIB 2.6 get-model response —
    //   ( (define-fun <sym> () <Sort> <value>) ... )
    // for every user-declared 0-arity symbol. Only meaningful after
    // checkSat() returned Sat.
    void dumpModel(std::ostream& os) const;

    // Independent self-check: does the last model satisfy the ORIGINAL
    // (pre-lowering) assertions? Uses a validator that shares no code with
    // the solver's own evaluators (defense-in-depth). Returns false ONLY on
    // a definite violation; an indeterminate result (UF, missing var,
    // unsupported construct) returns true ("not disproven"). This does NOT
    // affect the SAT verdict — it is a diagnostic for the Model-Validation
    // track and for tests. Meaningful only after checkSat() returned Sat.
    bool modelMatchesOriginal() const;

    // If the last checkSat returned Unknown, this gives a human-readable reason.
    std::string lastUnknownReason() const;

    // Structured unknown reason (code + component + detail)
    std::string lastUnknownCode() const;
    std::string lastUnknownComponent() const;
    std::string lastUnknownDetail() const;

    // Set path for per-case stats dump (--dump-stats)
    void setDumpStatsPath(std::string_view path);

    // Debug / research
    void dumpSMT2(std::ostream& os);

private:
    class Impl;
    std::unique_ptr<Impl> pImpl;
};

} // namespace zolver
