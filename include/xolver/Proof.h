#pragma once

#include <string>

namespace xolver {

/** Solver evidence from the preceding query. Alethe is an UNSAT artifact in
 * proof-enabled builds. Presburger obligations are available for SAT and UNSAT
 * on explicit request, including builds without ground-proof support. Native
 * QE obligations remain unverified until independently replayed against the
 * original input; this object does not assert that replay has succeeded.
 */
class Proof {
public:
    bool isEmpty() const { return alethe_.empty() && presburger_.empty(); }

    /// The Alethe theory-conflict refutation (empty when no certificate).
    const std::string& alethe() const { return alethe_; }

    /// The IR-derived SMT-LIB problem the Alethe proof is checked against.
    const std::string& problem() const { return problem_; }

    const std::string& presburger() const { return presburger_; }
    void setPresburger(std::string obligations) {
        clear();
        presburger_ = std::move(obligations);
    }
    void set(std::string alethe, std::string problem) {
        clear();
        alethe_ = std::move(alethe);
        problem_ = std::move(problem);
    }
    void clear() {
        alethe_.clear();
        problem_.clear();
        presburger_.clear();
    }

private:
    std::string presburger_;
    std::string alethe_;
    std::string problem_;
};

} // namespace xolver
