#include "search/refute/PolynomialConeRefutation.h"
#include "search/linear/NonnegativeWitness.h"
#include "search/lra/GeneralSimplex.h"
#include "base/RuntimeConfig.h"
#include <algorithm>
#include <deque>
#include <fstream>
#include <map>
#include <set>
#include <tuple>

namespace xolver {
namespace {
using Rule = PolynomialConeStep::Rule;

size_t degree(const RationalPolynomial& poly) {
    size_t result = 0;
    for (const auto& [word, coefficient] : poly.terms()) {
        (void)coefficient;
        size_t current = 0;
        for (const auto& [variable, exponent] : word) {
            (void)variable;
            if (exponent < 1 || exponent > 32) return 65;
            current += exponent;
        }
        result = std::max(result, current);
    }
    return result;
}

RationalPolynomial monomial(const MonomialKey& word) {
    RationalPolynomial result;
    result.addTerm(word, 1);
    result.normalize();
    return result;
}

PolynomialProof exportPolynomial(const RationalPolynomial& poly) {
    PolynomialProof result;
    for (const auto& [word, coefficient] : poly.terms())
        result.emplace(ProofMonomial(word.begin(), word.end()), coefficient);
    return result;
}

RationalPolynomial importPolynomial(const PolynomialProof& poly) {
    RationalPolynomial result;
    for (const auto& [word, coefficient] : poly) {
        MonomialKey key;
        for (const auto& power : word) key.push_back(power);
        result.addTerm(key, coefficient);
    }
    result.normalize();
    return result;
}

PolynomialConeCertificate prune(const PolynomialConeCertificate& input) {
    std::vector<bool> used(input.steps.size(), false);
    std::vector<size_t> pending;
    for (size_t i = 0; i < input.weights.size(); ++i)
        if (input.weights[i] != 0) pending.push_back(i);
    while (!pending.empty()) {
        const auto i = pending.back();
        pending.pop_back();
        if (used[i]) continue;
        used[i] = true;
        const auto& step = input.steps[i];
        if (step.rule == Rule::Product || step.rule == Rule::IntegralGap) pending.push_back(step.left);
        if (step.rule == Rule::Product) pending.push_back(step.right);
    }
    PolynomialConeCertificate result;
    std::vector<size_t> indices(input.steps.size());
    for (size_t i = 0; i < input.steps.size(); ++i) {
        if (!used[i]) continue;
        auto step = input.steps[i];
        if (step.rule == Rule::Product || step.rule == Rule::IntegralGap) step.left = indices[step.left];
        if (step.rule == Rule::Product) step.right = indices[step.right];
        indices[i] = result.steps.size();
        result.steps.push_back(std::move(step));
        result.weights.push_back(input.weights[i]);
    }
    return result;
}

class ConeSearch {
    const std::vector<SignRefuteConstraint>& constraints_;
    std::chrono::steady_clock::time_point deadline_;
    PolynomialDomain domain_;
    PolynomialConeStatistics& stats_;
    WorkBudget work_{200000};
    std::vector<PolynomialConePremise> sources_;
    PolynomialConeCertificate certificate_;
    struct Generator { RationalPolynomial poly; bool equality, strict; };
    std::vector<Generator> facts_;
    std::vector<PolynomialConeFact> replayFacts_;
    using Signature = std::tuple<bool, bool, std::vector<std::pair<MonomialKey, mpq_class>>>;
    std::map<Signature, size_t> emitted_;
    std::vector<size_t> base_;
    std::set<MonomialKey> words_;
    std::vector<RationalPolynomial> forms_;

    void tick(size_t amount = 1) {
        work_.tick(amount);
        if (std::chrono::steady_clock::now() >= deadline_)
            throw ResourceExhausted("polynomial cone allocation exhausted");
    }

    std::optional<size_t> add(PolynomialConeStep step) {
        tick();
        if (facts_.size() >= 512) { stats_.exhausted = true; return std::nullopt; }
        auto derived = derivePolynomialConeStep(step, sources_, replayFacts_, domain_, work_, deadline_);
        if (!derived) return std::nullopt;
        Generator fact{importPolynomial(derived->poly), derived->equality, derived->strict};
        if (degree(fact.poly) > 4 || (fact.poly.isZero() && !fact.strict)) return std::nullopt;
        if (!facts_.empty() && !fact.equality && fact.poly.isConstant() && fact.poly.constantValue() > 0)
            return size_t(0); // The unconditional strictly positive constant suffices.
        if (!fact.poly.isZero()) {
            step.scale = mpq_class(1) / abs(fact.poly.terms().front().second);
            fact.poly *= step.scale;
            for (auto& [word, coefficient] : derived->poly) { (void)word; coefficient *= step.scale; }
        }
        Signature signature{fact.equality, fact.strict,
            {fact.poly.terms().begin(), fact.poly.terms().end()}};
        if (const auto found = emitted_.find(signature); found != emitted_.end()) return found->second;
        const auto position = facts_.size();
        emitted_.emplace(std::move(signature), position);
        facts_.push_back(std::move(fact));
        replayFacts_.push_back(std::move(*derived));
        certificate_.steps.push_back(std::move(step));
        stats_.generators = facts_.size();
        return position;
    }

    void seed() {
        sources_.reserve(constraints_.size());
        words_.insert(MonomialKey{});
        for (const auto& constraint : constraints_) {
            tick();
            sources_.push_back({exportPolynomial(constraint.poly), constraint.rel});
            for (const auto& [word, coefficient] : constraint.poly.terms()) {
                (void)coefficient;
                if (degree(monomial(word)) <= 2) words_.insert(word);
                for (const auto& [variable, exponent] : word) {
                    (void)exponent;
                    words_.insert(MonomialKey{{variable, 1}});
                }
            }
        }
        add({}); // 1 is unconditionally strictly positive.
        for (size_t i = 0; i < sources_.size(); ++i) {
            tick();
            if (facts_.size() >= 512) { stats_.exhausted = true; break; }
            if (degree(constraints_[i].poly) > 4 || sources_[i].rel == Relation::Neq) continue;
            PolynomialConeStep step;
            step.rule = Rule::Premise;
            step.source = i;
            const auto source = add(std::move(step));
            if (!source) continue;
            if (facts_[*source].strict) {
                PolynomialConeStep rounded;
                rounded.rule = Rule::IntegralGap;
                rounded.left = *source;
                add(std::move(rounded));
            }
        }
        using Shape = std::vector<std::pair<MonomialKey, mpq_class>>;
        std::map<Shape, std::pair<mpq_class, size_t>> strongest;
        base_.push_back(0);
        for (size_t i = 1; i < facts_.size(); ++i) {
            if (facts_[i].equality) {
                if (degree(facts_[i].poly) <= 1) forms_.push_back(facts_[i].poly);
                continue;
            }
            const auto& terms = facts_[i].poly.terms();
            const auto first = std::find_if(terms.begin(), terms.end(), [](const auto& term) { return !term.first.empty(); });
            if (first == terms.end()) continue;
            const mpq_class scale = 1 / abs(first->second);
            Shape shape;
            mpq_class constant = 0;
            for (const auto& [word, coefficient] : terms) {
                if (word.empty()) constant = coefficient * scale;
                else shape.emplace_back(word, coefficient * scale);
            }
            auto found = strongest.find(shape);
            if (found == strongest.end() || constant < found->second.first ||
                (constant == found->second.first && facts_[i].strict && !facts_[found->second.second].strict))
                strongest.insert_or_assign(std::move(shape), std::make_pair(constant, i));
        }
        // Weaker parallel bounds are a stronger bound plus a positive constant.
        // Keeping one representative avoids quadratic duplication of products.
        for (const auto& [shape, entry] : strongest) {
            (void)shape;
            base_.push_back(entry.second);
            if (degree(facts_[entry.second].poly) <= 1) forms_.push_back(facts_[entry.second].poly);
        }
        forms_.push_back(RationalPolynomial::fromConstant(1));
        for (const auto& word : words_)
            if (word.size() == 1 && word.front().second == 1) forms_.push_back(monomial(word));
    }

    void extend(size_t maximumDegree) {
        // Equality multiples retain arbitrary coefficient signs in the LP.
        // Observed monomials and individual variables provide a finite basis.
        for (size_t source = 0; source < sources_.size(); ++source) {
            if (sources_[source].rel != Relation::Eq) continue;
            for (const auto& word : words_) {
                if (facts_.size() >= 512) { stats_.exhausted = true; return; }
                tick();
                auto factor = monomial(word);
                if (degree(constraints_[source].poly) + degree(factor) > maximumDegree) continue;
                PolynomialConeStep step;
                step.rule = Rule::EqualityMultiple;
                step.source = source;
                step.factor = exportPolynomial(factor);
                const auto before = facts_.size();
                add(std::move(step));
                stats_.equalityMultiples += facts_.size() != before;
            }
        }
        for (size_t i = 0; i < base_.size(); ++i) for (size_t j = i; j < base_.size(); ++j) {
            if (facts_.size() >= 512) { stats_.exhausted = true; return; }
            tick();
            if (degree(facts_[base_[i]].poly) + degree(facts_[base_[j]].poly) > maximumDegree) continue;
            PolynomialConeStep step;
            step.rule = Rule::Product;
            step.left = base_[i]; step.right = base_[j];
            const auto before = facts_.size();
            add(std::move(step));
            stats_.products += facts_.size() != before;
        }
    }

    void extendSquares(size_t maximumDegree) {
        // Differences need no sign premise: every rational polynomial square
        // is nonnegative, including at zero. They capture cross-variable terms.
        for (size_t i = 0; i < forms_.size(); ++i) for (size_t j = i; j < forms_.size(); ++j) {
            if (facts_.size() >= 512) { stats_.exhausted = true; return; }
            tick();
            PolynomialConeStep step;
            step.rule = Rule::Square;
            const auto factor = i == j ? forms_[i] : forms_[i] - forms_[j];
            if (2 * degree(factor) > maximumDegree) continue;
            step.factor = exportPolynomial(factor);
            const auto before = facts_.size();
            add(std::move(step));
            stats_.squares += facts_.size() != before;
        }
    }

    std::optional<PolynomialConeCertificate> solve() {
        tick();
        ++stats_.searches;
        // Equality coefficients are unrestricted. Quotient the coefficient
        // space by their span before asking Simplex for nonnegative weights.
        // Each elimination retains its exact combination of original equality
        // generators so no projected relation becomes a trusted assumption.
        using Coefficients = std::map<MonomialKey, mpq_class>;
        using Combination = std::map<size_t, mpq_class>;
        struct Equation { Coefficients polynomial; Combination proof; };
        std::map<MonomialKey, Equation> basis;
        auto checkCoefficient = [&](const mpq_class& coefficient) {
            if (mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) > 4096 ||
                mpz_sizeinbase(coefficient.get_den_mpz_t(), 2) > 4096)
                throw ResourceExhausted("polynomial coefficient projection limit");
        };
        auto addCoefficient = [&](auto& into, const auto& key, const mpq_class& value) {
            tick();
            auto& coefficient = into[key];
            coefficient += value;
            if (coefficient == 0) into.erase(key);
            else checkCoefficient(coefficient);
        };
        auto reduce = [&](Coefficients& polynomial, Combination& proof) {
            for (const auto& [pivot, equation] : basis) {
                tick();
                const auto found = polynomial.find(pivot);
                if (found == polynomial.end()) continue;
                const mpq_class factor = found->second;
                for (const auto& [word, coefficient] : equation.polynomial)
                    addCoefficient(polynomial, word, mpq_class(-factor * coefficient));
                for (const auto& [source, coefficient] : equation.proof)
                    addCoefficient(proof, source, mpq_class(-factor * coefficient));
            }
        };
        for (size_t i = 0; i < facts_.size(); ++i) {
            if (!facts_[i].equality) continue;
            tick();
            Equation equation{{facts_[i].poly.terms().begin(), facts_[i].poly.terms().end()}, {{i, 1}}};
            reduce(equation.polynomial, equation.proof);
            if (equation.polynomial.empty()) continue;
            const auto pivot = equation.polynomial.begin()->first;
            const mpq_class leading = equation.polynomial.begin()->second;
            for (auto& [word, coefficient] : equation.polynomial) {
                (void)word; tick(); coefficient /= leading; checkCoefficient(coefficient);
            }
            for (auto& [source, coefficient] : equation.proof) {
                (void)source; tick(); coefficient /= leading; checkCoefficient(coefficient);
            }
            basis.emplace(pivot, std::move(equation));
        }
        struct Projected { size_t generator; Coefficients polynomial; Combination proof; };
        std::vector<Projected> projected;
        for (size_t i = 0; i < facts_.size(); ++i) {
            if (facts_[i].equality) continue;
            tick();
            Projected row{i, {facts_[i].poly.terms().begin(), facts_[i].poly.terms().end()}, {}};
            reduce(row.polynomial, row.proof);
            projected.push_back(std::move(row));
        }
        auto witness = [&](const std::vector<mpq_class>& weights) {
            auto candidate = certificate_;
            candidate.weights.resize(facts_.size(), 0);
            for (size_t i = 0; i < weights.size(); ++i) {
                tick();
                if (weights[i] == 0) continue;
                candidate.weights[projected[i].generator] += weights[i];
                // residual = generator + sum proof[j]*equality[j].
                for (const auto& [source, coefficient] : projected[i].proof) {
                    tick();
                    candidate.weights[source] += weights[i] * coefficient;
                }
            }
            return prune(candidate);
        };
        // Parallel residuals describe the same nonnegative ray. Retain a
        // strict representative when available; the LP can absorb its scale.
        std::map<Coefficients, size_t> rays;
        std::vector<Projected> distinct;
        for (size_t i = 0; i < projected.size(); ++i) {
            tick();
            auto& row = projected[i];
            if (row.polynomial.empty()) {
                if (facts_[row.generator].strict) {
                    std::vector<mpq_class> weights(i + 1, 0);
                    weights[i] = 1;
                    return witness(weights);
                }
                continue;
            }
            auto direction = row.polynomial;
            const mpq_class scale = abs(direction.begin()->second);
            for (auto& [word, coefficient] : direction) {
                (void)word; tick(); coefficient /= scale; checkCoefficient(coefficient);
            }
            const auto [found, inserted] = rays.emplace(std::move(direction), distinct.size());
            if (inserted) distinct.push_back(std::move(row));
            else if (facts_[row.generator].strict) distinct[found->second] = std::move(row);
        }
        projected = std::move(distinct);
        // In a homogeneous coefficient row whose nonzero entries all have
        // one sign, every corresponding nonnegative weight must be zero.
        // Propagate that fact through the remaining rows before Simplex.
        struct Support {
            size_t positive = 0, negative = 0;
            std::vector<size_t> columns;
        };
        std::map<MonomialKey, Support> support;
        for (size_t i = 0; i < projected.size(); ++i)
            for (const auto& [word, coefficient] : projected[i].polynomial) {
                tick();
                auto& row = support[word];
                if (coefficient > 0) ++row.positive;
                else ++row.negative;
                row.columns.push_back(i);
            }
        std::deque<MonomialKey> pending;
        auto oneSign = [](const Support& row) { return (row.positive == 0) != (row.negative == 0); };
        for (const auto& [word, row] : support) if (oneSign(row)) pending.push_back(word);
        std::vector<bool> active(projected.size(), true);
        while (!pending.empty()) {
            tick();
            const auto word = std::move(pending.front());
            pending.pop_front();
            const auto& row = support.at(word);
            if (!oneSign(row)) continue;
            for (auto column : row.columns) {
                tick();
                if (!active[column]) continue;
                active[column] = false;
                for (const auto& [key, coefficient] : projected[column].polynomial) {
                    tick();
                    auto& changed = support.at(key);
                    if (coefficient > 0) --changed.positive;
                    else --changed.negative;
                    if (oneSign(changed)) pending.push_back(key);
                }
            }
        }
        distinct.clear();
        for (size_t i = 0; i < projected.size(); ++i)
            if (active[i]) distinct.push_back(std::move(projected[i]));
        projected = std::move(distinct);
        if (std::none_of(projected.begin(), projected.end(), [&](const auto& row) {
            return facts_[row.generator].strict;
        })) return std::nullopt;
        using Terms = std::vector<std::pair<size_t, mpq_class>>;
        std::map<MonomialKey, Terms> rows;
        NonnegativeEquation normalization{{}, 1};
        for (size_t i = 0; i < projected.size(); ++i) {
            tick();
            for (const auto& [word, coefficient] : projected[i].polynomial) {
                tick();
                rows[word].emplace_back(i, coefficient);
            }
            if (facts_[projected[i].generator].strict) normalization.coefficients.emplace_back(i, 1);
        }
        std::vector<NonnegativeEquation> equations;
        for (auto& [word, terms] : rows) { (void)word; equations.push_back({std::move(terms), 0}); }
        equations.push_back(std::move(normalization));
        stats_.coefficientRows = equations.size();
        if (auto weights = findNonnegativeWitness(projected.size(), equations, deadline_))
            return witness(*weights);

        GeneralSimplex simplex;
        std::vector<int> columns;
        std::vector<GeneralSimplex::ActiveBound> bounds;
        SatVar label = 0;
        for (size_t i = 0; i < projected.size(); ++i) {
            tick();
            const auto column = simplex.addVar("w" + std::to_string(i));
            columns.push_back(column);
            bounds.push_back({column, true, BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(++label))});
        }
        for (const auto& equation : equations) {
            tick(equation.coefficients.size() + 1);
            std::vector<std::pair<int, mpq_class>> terms;
            for (const auto& [column, coefficient] : equation.coefficients)
                terms.emplace_back(columns[column], coefficient);
            const auto row = simplex.addConstraint(terms, equation.rhs);
            if (row < 0) throw ResourceExhausted("polynomial coefficient row allocation failed");
            const BoundInfo zero(BoundValue(DeltaRational(0)), SatLit::positive(++label));
            bounds.push_back({row, true, zero});
            bounds.push_back({row, false, zero});
        }
        simplex.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve);
        const auto result = simplex.checkUntil(deadline_);
        if (result == GeneralSimplex::Result::Unknown) stats_.exhausted = true;
        if (result != GeneralSimplex::Result::Sat) return std::nullopt;
        const auto delta = simplex.computeSafeDelta();
        std::vector<mpq_class> weights;
        weights.reserve(columns.size());
        for (size_t i = 0; i < columns.size(); ++i) {
            tick();
            const auto value = simplex.value(columns[i]);
            weights.emplace_back(value.a + value.b * delta);
        }
        return witness(weights);
    }

public:
    ConeSearch(const std::vector<SignRefuteConstraint>& constraints,
               std::chrono::steady_clock::time_point deadline, PolynomialDomain domain,
               PolynomialConeStatistics& stats)
        : constraints_(constraints), deadline_(deadline), domain_(domain), stats_(stats) {}

    std::optional<std::vector<SatLit>> run(PolynomialConeCertificate* certificate) {
        seed();
        auto attempt = [&]() -> std::optional<std::vector<SatLit>> {
            const auto candidate = solve();
            if (!candidate) return std::nullopt;
            const auto proof = checkPolynomialConeCertificate(*candidate, sources_, domain_, deadline_);
            if (!proof) return std::nullopt;
            std::vector<SatLit> reasons;
            for (auto source : *proof) {
                const auto literal = constraints_[source].reason;
                if (!literal.var) return std::nullopt;
                if (std::find(reasons.begin(), reasons.end(), literal) == reasons.end()) reasons.push_back(literal);
            }
            if (reasons.empty()) return std::nullopt;
            stats_.certified = true;
            stats_.certificateSteps = candidate->steps.size();
            stats_.premises = reasons.size();
            if (certificate) *certificate = *candidate;
            return reasons;
        };
        for (size_t maximumDegree : {2U, 4U}) {
            const auto before = facts_.size();
            extend(maximumDegree);
            if (!stats_.searches || before != facts_.size())
                if (auto conflict = attempt()) return conflict;
            const auto products = facts_.size();
            extendSquares(maximumDegree);
            if (products != facts_.size()) if (auto conflict = attempt()) return conflict;
        }
        return std::nullopt;
    }
};
} // namespace

std::optional<std::vector<SatLit>> refuteByPolynomialCone(
    const std::vector<SignRefuteConstraint>& constraints,
    std::chrono::steady_clock::time_point deadline, PolynomialDomain domain,
    PolynomialConeStatistics* statistics, PolynomialConeCertificate* certificate) {
    PolynomialConeStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    if (certificate) *certificate = {};
    if (constraints.empty()) return std::nullopt;
    wall::DeadlineScope scope(deadline);
    const auto started = std::chrono::steady_clock::now();
    std::optional<std::vector<SatLit>> conflict;
    try {
        conflict = ConeSearch(constraints, wall::deadline(), domain, stats).run(certificate);
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    const auto profile = config::read<config::ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    if (!profile.empty()) {
        std::ofstream out(profile.string() + ".polynomial-cone.log", std::ios::app);
        out << "sources=" << constraints.size() << " generators=" << stats.generators
            << " rows=" << stats.coefficientRows << " searches=" << stats.searches
            << " products=" << stats.products << " squares=" << stats.squares
            << " equality_multiples=" << stats.equalityMultiples
            << " proof_steps=" << stats.certificateSteps << " premises=" << stats.premises
            << " certified=" << stats.certified << " exhausted=" << stats.exhausted
            << " us=" << std::chrono::duration_cast<std::chrono::microseconds>(
                std::chrono::steady_clock::now() - started).count() << '\n';
    }
    return conflict;
}

} // namespace xolver
