#pragma once

#include "theory/core/TheoryAtomTypes.h"
#include <functional>
#include <optional>
#include <string>
#include <utility>

namespace nlcolver {

class TheoryLemmaStorage;

/**
 * Reasoner — one stage of an arithmetic theory solver's check() pipeline.
 *
 * Architecture unification Phase 2. Each arith solver's check() used to be
 * a bespoke body (NRA: ~24 lines; NIA: ~337 lines of a hand-coded chain).
 * A Reasoner wraps a single coherent stage (a sub-engine or a
 * self-contained reasoning step) behind a uniform interface, so the
 * solver's check() becomes a uniform pipeline walk
 * (see ArithSolverBase::runReasonerPipeline).
 *
 * **Control-flow contract — the optional return.**
 * `run()` returns `std::optional<TheoryCheckResult>`:
 *   - `std::nullopt`            → this stage produced no verdict; the
 *                                 pipeline ADVANCES to the next stage.
 *   - `TheoryCheckResult{...}`  → this stage produced a verdict; the
 *                                 pipeline STOPS and returns it. This is
 *                                 true for Conflict / Lemma / Unknown AND
 *                                 for Consistent (a stage returning
 *                                 Consistent means "the whole theory state
 *                                 is consistent / SAT, stop here").
 *
 * This distinction matters: in the old linear check() bodies, every
 * `return consistent()` meant "stop, I'm done" — there was no implicit
 * "continue". Modeling "continue" as `nullopt` (rather than overloading
 * Consistent) reproduces the original control flow exactly.
 *
 * A Reasoner is NOT a stateless function: it owns / borrows whatever engine
 * or context it wraps. Those are wired in the owning solver's constructor.
 *
 * A Reasoner MUST NOT push onto the shared trail (state_.trail); only
 * assertLit does that (enforced by a debug assertion in the pipeline).
 */
class Reasoner {
public:
    virtual ~Reasoner() = default;

    // Human-readable identifier, used for trace output and stats.
    virtual std::string name() const = 0;

    // Effort gate. Reasoners that only make sense at Full effort return
    // false for Standard so the pipeline skips them.
    virtual bool runsAt(TheoryEffort effort) const {
        (void)effort;
        return true;
    }

    // The single check entry point. nullopt = continue; value = stop.
    virtual std::optional<TheoryCheckResult> run(TheoryLemmaStorage& lemmaDb,
                                                 TheoryEffort effort) = 0;
};

/**
 * CallbackReasoner — a concrete Reasoner backed by a std::function.
 *
 * Lets a solver decompose its check() into named stages without a separate
 * subclass per stage: the solver registers one CallbackReasoner per stage,
 * each wrapping a lambda (typically capturing `this` and calling a private
 * per-stage method). The stage logic stays inside the solver where it has
 * natural access to its members; the CallbackReasoner is the uniform
 * pipeline adapter.
 */
class CallbackReasoner : public Reasoner {
public:
    using Fn = std::function<std::optional<TheoryCheckResult>(
        TheoryLemmaStorage&, TheoryEffort)>;

    CallbackReasoner(std::string name, Fn fn,
                     bool fullEffortOnly = false)
        : name_(std::move(name)), fn_(std::move(fn)),
          fullEffortOnly_(fullEffortOnly) {}

    std::string name() const override { return name_; }

    bool runsAt(TheoryEffort effort) const override {
        if (fullEffortOnly_) return effort == TheoryEffort::Full;
        return true;
    }

    std::optional<TheoryCheckResult> run(TheoryLemmaStorage& lemmaDb,
                                         TheoryEffort effort) override {
        return fn_(lemmaDb, effort);
    }

private:
    std::string name_;
    Fn fn_;
    bool fullEffortOnly_;
};

} // namespace nlcolver
