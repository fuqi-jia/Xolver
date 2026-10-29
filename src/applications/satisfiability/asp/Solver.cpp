#include "applications/satisfiability/asp/Solver.h"
#include "search/optimization/BooleanOptimizer.h"
#include <algorithm>
#include <deque>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>

namespace xolver::applications::satisfiability::asp {
namespace {
using Boolean = std::vector<bool>;
Atom atomOf(Literal literal) {
    return static_cast<Atom>(literal < 0 ? -std::int64_t(literal) : literal);
}
struct Unsupported : std::runtime_error { using std::runtime_error::runtime_error; };
class Context {
    const Problem& problem_;
    SatSolver& sat_;
    bitblast::BitBlastEncoder encoder_;
    WorkBudget work_;
    bitblast::PseudoBooleanEncoder weights_;
    std::vector<Atom> atoms_;
    std::unordered_map<Atom, std::size_t> indices_;
    std::vector<SatLit> literals_;
    std::unordered_map<SatVar, std::size_t> satIndices_;
    std::vector<SatLit> bodies_;
    std::vector<std::vector<std::pair<std::size_t, mpz_class>>> incidence_;
    Boolean witness_;
    bool hasWitness_ = false;
public:
    std::size_t satCalls = 0, cuts = 0;
    Context(const Problem& problem, SatSolver& sat)
        : problem_(problem), sat_(sat), encoder_(sat), work_(problem.limits.formulaWork),
          weights_(encoder_, work_, problem.limits.deadline) {
        encoder_.setVarBudget(problem.limits.satVariables);
        sat_.setDeadline(problem.limits.deadline);
        std::set<Atom> referenced;
        auto literal = [&](Literal value) {
            if (!value || value == std::numeric_limits<Literal>::min())
                throw std::invalid_argument("invalid ASP atom literal");
            referenced.insert(atomOf(value));
        };
        for (const auto& rule : problem_.program.rules) {
            tick();
            if (!rule.choice && rule.head.size() > 1)
                throw Unsupported("disjunctive ASP rules are not supported");
            for (const auto head : rule.head) {
                if (!head || head > Atom(std::numeric_limits<Literal>::max()))
                    throw std::invalid_argument("invalid ASP head atom");
                referenced.insert(head);
            }
            for (const auto& term : rule.body) {
                literal(term.literal);
                if (term.weight < 0) throw Unsupported("negative weight in ASP rule body");
                if (!rule.weighted && term.weight != 1)
                    throw std::invalid_argument("normal ASP body literals must have unit weight");
            }
        }
        for (const auto& objective : problem_.program.objectives)
            for (const auto& term : objective.terms) literal(term.literal);
        for (const auto& output : problem_.program.output)
            for (const auto condition : output.condition) literal(condition);
        for (const auto assumption : problem_.program.assumptions) literal(assumption);
        atoms_.assign(referenced.begin(), referenced.end());
        for (std::size_t i = 0; i < atoms_.size(); ++i) {
            tick();
            indices_.emplace(atoms_[i], i);
            literals_.push_back(encoder_.mkVar(1).bits[0]);
            satIndices_.emplace(literals_.back().var, i);
        }
        incidence_.resize(atoms_.size());
        std::vector<std::vector<SatLit>> support(atoms_.size());
        for (std::size_t i = 0; i < problem_.program.rules.size(); ++i) {
            const auto& rule = problem_.program.rules[i];
            const auto body = encodeBody(rule);
            bodies_.push_back(body);
            if (!rule.choice) {
                if (rule.head.empty()) encoder_.assertLit(body.negated());
                else sat_.addClause({body.negated(), encoded(static_cast<Literal>(rule.head.front()))});
            }
            for (const auto head : rule.head) support[indices_.at(head)].push_back(body);
            for (const auto& term : rule.body)
                if (term.literal > 0)
                    incidence_[indices_.at(atomOf(term.literal))].push_back({i, term.weight});
        }
        for (std::size_t i = 0; i < atoms_.size(); ++i) {
            auto justified = encoder_.constFalse();
            for (const auto body : support[i]) justified = encoder_.orGate(justified, body);
            sat_.addClause({literals_[i].negated(), justified});
        }
        for (const auto assumption : problem_.program.assumptions) encoder_.assertLit(encoded(assumption));
        tick();
    }
    void tick(std::size_t amount = 1) {
        work_.tick(amount);
        if (problem_.limits.stop.stop_requested()) throw ResourceExhausted("ASP cancelled");
        if (std::chrono::steady_clock::now() >= problem_.limits.deadline)
            throw ResourceExhausted("ASP deadline exhausted");
        if (encoder_.overflowed()) throw ResourceExhausted("ASP SAT-variable budget exhausted");
    }
    SatLit encoded(Literal literal) const {
        const auto atom = literals_.at(indices_.at(atomOf(literal)));
        return literal > 0 ? atom : atom.negated();
    }
    bool truth(Literal literal, const Boolean& model) const {
        return model[indices_.at(atomOf(literal))] == (literal > 0);
    }
    bool bodyHolds(const Rule& rule, const Boolean& positive, const Boolean& negative,
                   const Boolean* excluded = nullptr) {
        mpz_class sum = 0;
        for (const auto& term : rule.body) {
            tick();
            const auto i = indices_.at(atomOf(term.literal));
            const bool holds = term.literal > 0
                ? positive[i] && (!excluded || !(*excluded)[i]) : !negative[i];
            if (!rule.weighted && !holds) return false;
            if (holds) sum += term.weight;
        }
        return !rule.weighted || sum >= rule.lowerBound;
    }
    SatLit encodeBody(const Rule& rule, const Boolean* excluded = nullptr) {
        tick();
        if (!rule.weighted) {
            auto body = encoder_.constTrue();
            for (const auto& term : rule.body) {
                tick();
                if (excluded && term.literal > 0 && (*excluded)[indices_.at(atomOf(term.literal))])
                    return encoder_.constFalse();
                body = encoder_.andGate(body, encoded(term.literal));
            }
            tick();
            return body;
        }
        std::vector<bitblast::WeightedLiteral> terms;
        for (const auto& term : rule.body) {
            tick();
            if (!excluded || term.literal < 0 || !(*excluded)[indices_.at(atomOf(term.literal))])
                terms.push_back({encoded(term.literal), term.weight});
        }
        const auto below = weights_.lessEqual(std::move(terms), rule.lowerBound-1);
        if (!below) throw ResourceExhausted("ASP weighted-body encoding exhausted");
        tick();
        return below->negated();
    }
    Boolean leastReduct(const Boolean& candidate) {
        const auto& rules = problem_.program.rules;
        std::vector<mpz_class> remaining(rules.size());
        std::vector<bool> disabled(rules.size(), false), fired(rules.size(), false);
        Boolean least(atoms_.size(), false);
        std::deque<std::size_t> queue;
        for (std::size_t r = 0; r < rules.size(); ++r) {
            const auto& rule = rules[r];
            remaining[r] = rule.weighted ? rule.lowerBound : mpz_class(0);
            for (const auto& term : rule.body) {
                tick();
                if (term.literal > 0) {
                    if (!rule.weighted) ++remaining[r];
                } else if (truth(term.literal, candidate)) {
                    if (rule.weighted) remaining[r] -= term.weight;
                } else if (!rule.weighted) disabled[r] = true;
            }
        }
        auto fire = [&](std::size_t r) {
            if (fired[r] || disabled[r] || remaining[r] > 0) return;
            fired[r] = true;
            for (const auto head : rules[r].head) {
                const auto i = indices_.at(head);
                if ((!rules[r].choice || candidate[i]) && !least[i]) {
                    least[i] = true;
                    queue.push_back(i);
                }
            }
        };
        for (std::size_t r = 0; r < rules.size(); ++r) fire(r);
        while (!queue.empty()) {
            const auto atom = queue.front();
            queue.pop_front();
            for (const auto& [r, weight] : incidence_[atom]) {
                tick();
                remaining[r] -= rules[r].weighted ? weight : mpz_class(1);
                fire(r);
            }
        }
        return least;
    }
    SatSolver::SolveResult check(const std::vector<SatLit>& assumptions) {
        for (;;) {
            tick();
            if (problem_.limits.satCalls && satCalls >= problem_.limits.satCalls)
                throw ResourceExhausted("ASP SAT-call budget exhausted");
            ++satCalls;
            const auto result = sat_.solve(assumptions);
            if (result != SatSolver::SolveResult::Sat) return result;
            Boolean candidate;
            for (const auto lit : literals_) candidate.push_back(sat_.value(lit.var) == lit.sign);
            for (const auto& rule : problem_.program.rules) {
                if (rule.choice || !bodyHolds(rule, candidate, candidate)) continue;
                if (rule.head.empty() || !candidate[indices_.at(rule.head.front())])
                    throw std::runtime_error("ASP SAT model violates an original rule");
            }
            for (const auto assumption : problem_.program.assumptions)
                if (!truth(assumption, candidate)) throw std::runtime_error("ASP model violates an assumption");
            const auto least = leastReduct(candidate);
            if (least == candidate) {
                witness_ = std::move(candidate);
                hasWitness_ = true;
                return SatSolver::SolveResult::Sat;
            }
            Boolean unfounded(atoms_.size(), false);
            bool nonempty = false;
            for (std::size_t i = 0; i < candidate.size(); ++i) {
                if (least[i] && !candidate[i]) throw std::runtime_error("ASP reduct exceeds its candidate");
                nonempty |= (unfounded[i] = candidate[i] && !least[i]);
            }
            if (!nonempty) throw std::runtime_error("ASP stability refinement made no progress");
            auto external = encoder_.constFalse();
            for (const auto& rule : problem_.program.rules) {
                bool headInside = false;
                for (const auto head : rule.head) headInside |= unfounded[indices_.at(head)];
                if (!headInside) continue;
                if (bodyHolds(rule, candidate, candidate, &unfounded))
                    throw std::runtime_error("ASP unfounded set has candidate external support");
                external = encoder_.orGate(external, encodeBody(rule, &unfounded));
            }
            tick();
            // Every stable model with any atom in this set needs support that
            // does not depend positively on the set itself. The threshold body
            // is re-evaluated with those positive contributions removed.
            for (std::size_t i = 0; i < unfounded.size(); ++i)
                if (unfounded[i]) sat_.addClause({literals_[i].negated(), external});
            ++cuts;
        }
    }
    Answer run() {
        Answer answer;
        std::vector<::xolver::optimization::BooleanObjective> objectives;
        for (const auto& original : problem_.program.objectives) {
            ::xolver::optimization::BooleanObjective objective;
            objective.priority = original.priority;
            for (const auto& term : original.terms)
                objective.terms.push_back({encoded(term.literal), term.weight});
            objectives.push_back(std::move(objective));
        }
        const auto optimum = ::xolver::optimization::minimizeBooleanLex(encoder_, work_, objectives,
            [&](const auto& assumptions) { return check(assumptions); },
            [&](SatLit literal) {
                // Objective literals refer to program atoms, not Tseitin gates.
                return witness_.at(satIndices_.at(literal.var)) == literal.sign;
            }, problem_.limits.deadline);
        answer.provedLevels = optimum.provedLevels;
        answer.reason = optimum.reason;
        if (optimum.status == ::xolver::optimization::BooleanOptimum::Status::Infeasible)
            answer.status = Status::Unsat;
        else if (optimum.status == ::xolver::optimization::BooleanOptimum::Status::Optimal)
            answer.status = objectives.empty() ? Status::Sat : Status::Optimal;
        retain(answer);
        return answer;
    }
    void retain(Answer& answer) const {
        answer.satCalls = satCalls;
        answer.unfoundedCuts = cuts;
        if (!hasWitness_) return;
        answer.model.emplace();
        answer.atomIds = atoms_;
        for (std::size_t i = 0; i < atoms_.size(); ++i)
            if (witness_[i]) answer.model->push_back(atoms_[i]);
        std::set<std::string> shownLabels;
        for (const auto& output : problem_.program.output) {
            bool shown = true;
            for (const auto condition : output.condition) shown &= truth(condition, witness_);
            if (shown && shownLabels.insert(output.text).second) answer.shown.push_back(output.text);
        }
        std::map<std::int64_t, mpz_class, std::greater<>> costs;
        for (const auto& objective : problem_.program.objectives)
            for (const auto& term : objective.terms) {
                auto& cost = costs[objective.priority];
                if (truth(term.literal, witness_)) cost += term.weight;
            }
        for (const auto& objective : problem_.program.objectives) costs.try_emplace(objective.priority, 0);
        for (const auto& [priority, cost] : costs) {
            answer.priorities.push_back(priority);
            answer.costs.push_back(cost);
        }
    }
};
}

Answer Solver::solve(const Problem& problem) {
    Answer answer;
    if (!factory_) { answer.reason = "ASP SAT backend factory is not attached"; return answer; }
    std::unique_ptr<SatSolver> backend;
    std::unique_ptr<Context> context;
    try {
        backend = factory_();
        if (!backend) { answer.reason = "ASP SAT backend factory returned null"; return answer; }
        context = std::make_unique<Context>(problem, *backend);
        try { answer = context->run(); }
        catch (const ResourceExhausted& error) { answer.reason = error.what(); context->retain(answer); }
        // Context owns encoding references into backend; destroy it first.
        context.reset();
    } catch (const Unsupported& error) {
        answer.status = Status::Unsupported;
        answer.reason = error.what();
    } catch (const std::invalid_argument& error) {
        answer.status = Status::InvalidInput;
        answer.reason = error.what();
    } catch (const std::exception& error) {
        answer.reason = error.what();
    }
    return answer;
}

} // namespace xolver::applications::satisfiability::asp
