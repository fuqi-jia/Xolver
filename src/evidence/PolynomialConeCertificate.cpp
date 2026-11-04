#include "evidence/PolynomialConeCertificate.h"
#include "base/RationalLattice.h"
#include <algorithm>

namespace xolver {
namespace {
void include(std::vector<size_t>& into, const std::vector<size_t>& from) {
    for (auto source : from)
        if (std::find(into.begin(), into.end(), source) == into.end()) into.push_back(source);
}
void removeZeros(PolynomialProof& poly) {
    for (auto it = poly.begin(); it != poly.end();)
        if (it->second == 0) it = poly.erase(it);
        else ++it;
}
} // namespace

std::optional<PolynomialConeFact> derivePolynomialConeStep(
    const PolynomialConeStep& step, const std::vector<PolynomialConePremise>& sources,
    const std::vector<PolynomialConeFact>& preceding, PolynomialDomain domain,
    WorkBudget& work, std::chrono::steady_clock::time_point deadline) {
    auto tick = [&](size_t amount = 1) {
        work.tick(amount);
        if (std::chrono::steady_clock::now() >= deadline)
            throw ResourceExhausted("polynomial certificate allocation exhausted");
    };
    auto checked = [&](const PolynomialProof& poly) {
        if (poly.size() > 256) throw ResourceExhausted("polynomial certificate term limit");
        for (const auto& [word, coefficient] : poly) {
            tick(1 + word.size());
            if (coefficient.get_den() <= 0) return false;
            if (mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) > 4096 ||
                mpz_sizeinbase(coefficient.get_den_mpz_t(), 2) > 4096)
                throw ResourceExhausted("polynomial certificate coefficient limit");
            VarId previous = 0;
            bool first = true;
            for (const auto& [variable, exponent] : word) {
                if (exponent < 1 || exponent > 32 || (!first && variable <= previous)) return false;
                previous = variable;
                first = false;
            }
        }
        return true;
    };
    // The verifier uses its own sparse map arithmetic. It does not link the
    // solver's RationalPolynomial, polynomial kernel, Simplex or search code.
    auto multiply = [&](const PolynomialProof& a, const PolynomialProof& b) {
        if (!checked(a) || !checked(b)) throw ResourceExhausted("invalid certificate polynomial");
        if (!a.empty() && b.size() > 4096 / a.size())
            throw ResourceExhausted("polynomial certificate product limit");
        PolynomialProof result;
        for (const auto& [left, ca] : a) for (const auto& [right, cb] : b) {
            tick(1 + left.size() + right.size());
            ProofMonomial word;
            size_t i = 0, j = 0;
            while (i < left.size() || j < right.size()) {
                if (j == right.size() || (i < left.size() && left[i].first < right[j].first))
                    word.push_back(left[i++]);
                else if (i == left.size() || right[j].first < left[i].first)
                    word.push_back(right[j++]);
                else {
                    word.emplace_back(left[i].first, left[i].second + right[j].second);
                    ++i; ++j;
                }
            }
            result[std::move(word)] += ca * cb;
        }
        removeZeros(result);
        return result;
    };
    tick();
    if (step.scale.get_den() <= 0 || step.scale <= 0 ||
        mpz_sizeinbase(step.scale.get_num_mpz_t(), 2) > 4096 ||
        mpz_sizeinbase(step.scale.get_den_mpz_t(), 2) > 4096) return std::nullopt;
    PolynomialConeFact result;
    using Rule = PolynomialConeStep::Rule;
    switch (step.rule) {
        case Rule::One:
            result.poly[{}] = 1;
            result.strict = true;
            break;
        case Rule::Premise: {
            if (step.source >= sources.size()) return std::nullopt;
            const auto& source = sources[step.source];
            if (source.rel != Relation::Eq && source.rel != Relation::Lt && source.rel != Relation::Leq &&
                source.rel != Relation::Gt && source.rel != Relation::Geq) return std::nullopt;
            if (!checked(source.poly)) return std::nullopt;
            result.poly = source.poly;
            if (source.rel == Relation::Lt || source.rel == Relation::Leq)
                for (auto& [word, coefficient] : result.poly) { (void)word; coefficient = -coefficient; }
            result.equality = source.rel == Relation::Eq;
            result.strict = source.rel == Relation::Lt || source.rel == Relation::Gt;
            result.sources = {step.source};
            break;
        }
        case Rule::IntegralGap: {
            if (step.left >= preceding.size()) return std::nullopt;
            const auto& parent = preceding[step.left];
            if (parent.equality || !parent.strict || !checked(parent.poly)) return std::nullopt;
            const auto gap = rationalLatticeStep(parent.poly, [&](VarId variable) {
                return domain.allInteger || std::find(domain.integerVariables.begin(),
                    domain.integerVariables.end(), variable) != domain.integerVariables.end();
            }, tick);
            if (!gap) return std::nullopt;
            result.poly = parent.poly;
            result.poly[{}] -= *gap;
            result.sources = parent.sources;
            break;
        }
        case Rule::Square:
            result.poly = multiply(step.factor, step.factor);
            break;
        case Rule::Product: {
            if (step.left >= preceding.size() || step.right >= preceding.size()) return std::nullopt;
            const auto& left = preceding[step.left];
            const auto& right = preceding[step.right];
            if (left.equality || right.equality) return std::nullopt;
            result.poly = multiply(left.poly, right.poly);
            result.strict = left.strict && right.strict;
            result.sources = left.sources;
            include(result.sources, right.sources);
            break;
        }
        case Rule::EqualityMultiple:
            if (step.source >= sources.size() || sources[step.source].rel != Relation::Eq) return std::nullopt;
            result.poly = multiply(sources[step.source].poly, step.factor);
            result.equality = true;
            result.sources = {step.source};
            break;
        default: return std::nullopt;
    }
    for (auto& [word, coefficient] : result.poly) {
        tick(word.size() + 1);
        coefficient *= step.scale;
    }
    removeZeros(result.poly);
    if (!checked(result.poly)) return std::nullopt;
    return result;
}

std::optional<std::vector<size_t>> checkPolynomialConeCertificate(
    const PolynomialConeCertificate& certificate, const std::vector<PolynomialConePremise>& sources,
    PolynomialDomain domain, std::chrono::steady_clock::time_point deadline) {
    if (certificate.steps.size() != certificate.weights.size() || certificate.steps.size() > 1024)
        return std::nullopt;
    try {
        WorkBudget work(200000);
        std::vector<PolynomialConeFact> derived;
        PolynomialProof identity;
        std::vector<size_t> premises;
        bool strict = false;
        for (size_t i = 0; i < certificate.steps.size(); ++i) {
            const auto fact = derivePolynomialConeStep(certificate.steps[i], sources, derived, domain, work, deadline);
            if (!fact) return std::nullopt;
            derived.push_back(*fact);
            const auto& coefficient = certificate.weights[i];
            if (coefficient.get_den() <= 0 || (!fact->equality && coefficient < 0) ||
                mpz_sizeinbase(coefficient.get_num_mpz_t(), 2) > 4096 ||
                mpz_sizeinbase(coefficient.get_den_mpz_t(), 2) > 4096) return std::nullopt;
            if (coefficient == 0) continue;
            for (const auto& [word, value] : fact->poly) {
                work.tick(word.size() + 1);
                identity[word] += value * coefficient;
            }
            include(premises, fact->sources);
            strict |= fact->strict && coefficient > 0;
        }
        work.tick(identity.size() + 1);
        if (std::chrono::steady_clock::now() >= deadline) return std::nullopt;
        removeZeros(identity);
        if (strict && identity.empty() && !premises.empty()) return premises;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
    return std::nullopt;
}

} // namespace xolver
