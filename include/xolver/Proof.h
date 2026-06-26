#pragma once

#include <string>

namespace xolver {

/**
 * An UNSAT proof produced by the solver.
 *
 * Populated only in proof-enabled builds (-DXOLVER_ENABLE_PROOFS=ON) when the
 * preceding checkSat() returned Unsat with a single-conflict theory certificate;
 * otherwise it is empty (the unsat is still sound, just not independently
 * certified here — the degraded path). The Alethe text is the same artifact
 * `solve --produce-proof` writes to <base>.alethe, checkable by Carcara against
 * problem(): `carcara check <alethe> <problem>`.
 */
class Proof {
public:
    bool isEmpty() const { return alethe_.empty(); }

    /// The Alethe theory-conflict refutation (empty when no certificate).
    const std::string& alethe() const { return alethe_; }

    /// The IR-derived SMT-LIB problem the Alethe proof is checked against.
    const std::string& problem() const { return problem_; }

    void set(std::string alethe, std::string problem) {
        alethe_ = std::move(alethe);
        problem_ = std::move(problem);
    }
    void clear() {
        alethe_.clear();
        problem_.clear();
    }

private:
    std::string alethe_;
    std::string problem_;
};

} // namespace xolver
