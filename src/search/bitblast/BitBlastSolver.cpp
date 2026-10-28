#include "base/RuntimeConfig.h"
#include "search/bitblast/BitBlastSolver.h"
#include "base/SolveClock.h"
#include "search/bitblast/BitBlastEncoder.h"
#include "search/bitblast/PolyBitBlaster.h"
#include "contracts/SatSolver.h"
#include <chrono>
#include <string>
#include <unordered_map>
#include <algorithm>
#include <iostream>

namespace xolver::bitblast {

uint64_t BitBlastSolver::defaultGateBudget() {
    // Max fresh SAT variables the bit-blast encoder may allocate. Both the
    // encoding AND the subsequent CaDiCaL solve consume memory; empirically a
    // 2 GB process OOMs (bad_alloc) somewhere between ~0.2M and ~0.5M vars on
    // dense high-degree QF_NIA. 200k stays safely under that, keeps the curated
    // NIA suite (tiny encodings) unaffected, and turns the AProVE blow-ups into
    // a clean Unknown. Env-tunable: competition runs with more RAM should raise
    // XOLVER_NIA_BITBLAST_GATE_BUDGET to solve larger bounded instances.
    {
        long long v = config::read<config::ReadKind::Long>("XOLVER_NIA_BITBLAST_GATE_BUDGET", 2000000);
        if (v > 0) return static_cast<uint64_t>(v);
    }
    // Competition retune: 30GB (not the dev 2GB) allows far more vars before OOM
    // (~0.2-0.5M vars per 2GB => ~3-7M for 30GB). 2M is safely under that and lets
    // the bit-blast decide larger bounded instances; tiny suite encodings are
    // unaffected. Overflow past the cap still bails to a clean Unknown (sound).
    return 2000000ull;
}

bool BitBlastSolver::applicable(const std::vector<NormalizedNiaConstraint>& cs) const {
    for (const auto& c : cs) {
        if (!kernel_.terms(c.poly)) return false;   // need monomial decomposition
    }
    return true;
}

bool BitBlastSolver::encodeDomainBounds(
    BitBlastEncoder& enc,
    const std::unordered_map<std::string, BitVec>& varBits,
    const DomainStore& domains, std::vector<EncodedFact>& facts) {
    // Confine the SAT search to the DomainStore box so the search space EQUALS
    // [lb,ub]^n ∩ cs (not the raw two's-complement width range).
    for (const auto& kv : varBits) {
        if (enc.overflowed() || enc.inconsistent()) return false;
        const IntDomain* d = domains.getDomain(kv.first);
        if (!d) continue;
        const BitVec& x = kv.second;
        auto append = [&](SatLit literal) {
            if (enc.overflowed()) return false;
            facts.push_back({literal, 0, &kv.first});
            return literal != enc.constFalse();
        };
        if (x.width() > 0) {
            if (d->hasUpper && d->upper.value < 0) {
                if (!append(x.sign())) return false;
            } else if (d->hasLower && d->lower.value >= 0) {
                if (!append(x.sign().negated())) return false;
            }
        }
        if (d->hasLower && !append(enc.relZero(
                enc.sub(x, enc.mkConst(d->lower.value)), Relation::Geq))) return false;
        if (d->hasUpper && !append(enc.relZero(
                enc.sub(x, enc.mkConst(d->upper.value)), Relation::Leq))) return false;
        if (d->finiteValues) {
            SatLit member = enc.constFalse();
            for (const auto& v : *d->finiteValues) {
                member = enc.orGate(member, enc.eq(x, enc.mkConst(v)));
                if (enc.overflowed()) return false;
            }
            if (!append(member)) return false;
        }
        for (const auto& ex : d->excludedValues)
            if (!append(enc.relZero(enc.sub(x, enc.mkConst(ex.first)), Relation::Neq)))
                return false;
    }
    return true;
}

bool BitBlastSolver::modelInDomains(const IntegerModel& model, const DomainStore& domains) {
    for (const auto& entry : domains.getAllDomains()) {
        const std::string& var = entry.first;
        const IntDomain& d = entry.second;
        auto it = model.find(var);
        if (it == model.end()) continue;            // var not encoded; nothing to check
        const mpz_class& v = it->second;
        if (d.hasLower && v < d.lower.value) return false;
        if (d.hasUpper && v > d.upper.value) return false;
        if (d.finiteValues && d.finiteValues->count(v) == 0) return false;
        if (d.excludedValues.count(v)) return false;
    }
    return true;
}

std::optional<TheoryConflict> BitBlastSolver::buildCompleteConflict(
    const std::vector<NormalizedNiaConstraint>& cs, const DomainStore& domains,
    const std::unordered_set<std::string>* variables) const {
    // The encoded conjunction (all cs constraints AND every encoded domain
    // restriction) is infeasible over the complete box, so the negation of
    // EVERY justifying reason literal is a sound theory lemma. CRITICAL: every
    // restriction we encoded must contribute its reason. If any encoded
    // restriction has NO usable reason, we cannot prove the conjunction sound —
    // silently dropping it would yield an UNSOUND conflict (e.g. "¬A ∨ ¬B" when
    // the real infeasibility also needed an unjustified bound). So we bail to
    // Unknown rather than emit a partial conflict.
    //
    // POLARITY: reasons are stored in their *asserted* (true-under-model) form,
    // matching the NIA convention (see DomainStore::buildEmptyDomainConflict).
    // TheoryManager::makeFalsifiedConflict negates them into the falsified
    // clause `⋁ ¬reason`. Negating here would double-negate and produce an
    // all-true clause the propagator rejects (UnsatComplete → silently lost).
    TheoryConflict cf;

    auto pushAll = [&](const std::vector<SatLit>& reasons) -> bool {
        if (reasons.empty()) return false;
        for (const auto& l : reasons) {
            if (l.var == 0) return false;
            cf.clause.push_back(l);
        }
        return true;
    };
    auto pushOne = [&](SatLit l) -> bool {
        if (l.var == 0) return false;
        cf.clause.push_back(l);
        return true;
    };

    for (const auto& c : cs) {
        if (!pushOne(c.reason)) return std::nullopt;
    }
    for (const auto& entry : domains.getAllDomains()) {
        if (variables && !variables->contains(entry.first)) continue;
        const IntDomain& d = entry.second;
        if (d.hasLower && !pushAll(d.lower.reasons)) return std::nullopt;
        if (d.hasUpper && !pushAll(d.upper.reasons)) return std::nullopt;
        if (d.finiteValues && !pushAll(d.finiteSetReasons)) return std::nullopt;
        for (const auto& ex : d.excludedValues) {
            if (!pushAll(ex.second)) return std::nullopt;
        }
    }

    if (cf.clause.empty()) return std::nullopt;
    if (!normalizeTheoryClause(cf.clause)) return std::nullopt;
    return cf;
}

// One encode+solve+validate attempt at a fixed width plan. Returns the raw
// outcome (Sat carries a validated in-box model; Unsat is box-dependent — the
// caller decides whether it is globally complete; Overflow = encoding exceeded
// the var budget). All width plans share this encoding/validation path.
BitBlastSolver::Attempt BitBlastSolver::attemptAtWidths(
    const BitWidthPlan& plan,
    const std::vector<NormalizedNiaConstraint>& cs,
    const DomainStore& domains,
    const IntegerModelValidator& validator) {
    // Finer profiler (NIA_BITBLAST_PROF): split encode-vs-SAT time + attempts,
    // dumped to stderr every 2s so a timeout-killed run still reveals the
    // dominant bit-blast cost (no clean exit). Zero cost when env unset.
    const bool bbProf = xolver::config::read<xolver::config::ReadKind::Presence>("NIA_BITBLAST_PROF");
    struct BBProf {
        double encodeMs = 0, satMs = 0; long attempts = 0; long lastVars = 0;
        std::chrono::steady_clock::time_point lastDump = std::chrono::steady_clock::now();
        void maybeDump() {
            auto now = std::chrono::steady_clock::now();
            if (std::chrono::duration_cast<std::chrono::milliseconds>(now - lastDump).count() >= 2000) {
                std::cerr << "[BB-PROF] attempts=" << attempts << " encode_ms=" << (long)encodeMs
                          << " sat_ms=" << (long)satMs << " last_satvars=" << lastVars << "\n";
                lastDump = now;
            }
        }
    };
    static BBProf prof;

    Attempt a;
    auto sat = createSatSolver();
    // Keep gate extraction disabled on this dedicated SAT solver: its
    // occurrence table caused excessive memory use on large DT+NIA encodings.
    // The remaining SAT preprocessing and model validation run normally.
    sat->configure("congruence", 0);
    if (satConflictBudget_ > 0) {
        // Cap CaDiCaL's conflicts for THIS internal solve. CaDiCaL returns
        // UNKNOWN when the limit is hit, which the bit-blast treats as
        // "this width didn't decide" and falls through (sound).
        sat->limit("conflicts", static_cast<int>(satConflictBudget_));
    }
    BitBlastEncoder enc(*sat);
    enc.setVarBudget(gateBudget_);   // hard cap: stop encoding before OOM
    std::unordered_map<std::string, BitVec> varBits;
    auto encT0 = std::chrono::steady_clock::now();
    for (const auto& kv : plan.width) varBits[kv.first] = enc.mkVar(kv.second);

    PolyBitBlaster blaster(enc, kernel_, varBits);
    std::vector<EncodedFact> facts;
    facts.reserve(cs.size() + 2 * varBits.size());
    size_t encoded = 0;
    bool full = true;
    for (size_t index = 0; index < cs.size(); ++index) {
        if (enc.overflowed() || enc.inconsistent()) { full = false; break; }
        const auto literal = blaster.encodeConstraint(cs[index]);
        if (enc.overflowed()) { full = false; break; }
        facts.push_back({literal, index, nullptr});
        ++encoded;
        if (literal == enc.constFalse()) { full = false; break; }
    }
    if (full) full = encodeDomainBounds(enc, varBits, domains, facts);
    if (bbProf) {
        std::cerr << "[BB-PREFIX] encoded=" << encoded << '/' << cs.size()
                  << " satvars=" << enc.varCount()
                  << " root_conflict=" << (!enc.overflowed() && enc.inconsistent())
                  << " overflow=" << enc.overflowed()
                  << " encode_ms=" << std::chrono::duration<double, std::milli>(
                      std::chrono::steady_clock::now() - encT0).count() << '\n';
        prof.encodeMs += std::chrono::duration<double, std::milli>(
                             std::chrono::steady_clock::now() - encT0).count();
        ++prof.attempts; prof.lastVars = (long)enc.varCount(); prof.maybeDump();
    }

    // Gates and assertions emit no clauses after allocation fails. Thus the
    // completed facts still describe an exact prefix; never assume a fact
    // whose own encoding overflowed. SAT needs the entire encoding, while a
    // complete refutation of this prefix can already settle the query.
    if (facts.empty()) {
        if (enc.overflowed()) a.kind = Attempt::Overflow;
        return a;
    }
    std::vector<SatLit> assumptions;
    assumptions.reserve(facts.size());
    for (const auto& fact : facts) assumptions.push_back(fact.literal);

    auto satT0 = std::chrono::steady_clock::now();
    auto res = sat->solve(assumptions);
    if (bbProf) {
        prof.satMs += std::chrono::duration<double, std::milli>(
                          std::chrono::steady_clock::now() - satT0).count();
        prof.maybeDump();
    }
    const bool bbDiag = xolver::config::read<xolver::config::ReadKind::Presence>("NIA_BITBLAST_DIAG");
    if (res == SatSolver::SolveResult::Sat) {
        if (!full || enc.overflowed()) {
            if (enc.overflowed()) a.kind = Attempt::Overflow;
            return a;
        }
        IntegerModel model;
        for (const auto& kv : varBits) model[kv.first] = readBitVec(*sat, kv.second);
        // Accept only a model that satisfies cs (exact) AND lies in the box.
        bool valid = validator.validate(model, cs) == IntegerModelValidator::Result::Valid;
        bool inBox = modelInDomains(model, domains);
        if (bbDiag) {
            std::cerr << "[BB-DIAG] SAT@vars=" << enc.varCount() << " valid=" << valid
                      << " inBox=" << inBox;
            if (!valid || !inBox) { for (const auto& kv : model) std::cerr << " " << kv.first << "=" << kv.second.get_str(); }
            std::cerr << "\n";
        }
        if (valid && inBox) {
            a.kind = Attempt::Sat;
            a.model = std::move(model);
        }
        // else: SAT under narrow widths but not a real / in-box model — artifact (Unknown).
        return a;
    }
    if (res == SatSolver::SolveResult::Unsat) {
        if (bbDiag) std::cerr << "[BB-DIAG] UNSAT@vars=" << enc.varCount() << "\n";
        a.kind = Attempt::Unsat;
        const auto failed = sat->getFailedAssumptions();
        const auto key = [](SatLit literal) {
            return (uint64_t(literal.var) << 1) | unsigned(literal.sign);
        };
        std::unordered_set<uint64_t> failedKeys;
        for (const auto literal : failed) failedKeys.insert(key(literal));
        struct Source {
            const EncodedFact* fact;
            std::vector<std::string> variables;
            size_t unbounded;
        };
        std::unordered_map<uint64_t, Source> selected;
        for (const auto& fact : facts) {
            const auto id = key(fact.literal);
            if (!failedKeys.contains(id)) continue;
            auto variables = fact.domainVariable
                ? std::vector<std::string>{*fact.domainVariable}
                : kernel_.variables(cs[fact.constraint].poly);
            size_t unbounded = 0;
            for (const auto& variable : variables) {
                const auto* d = domains.getDomain(variable);
                unbounded += !d || !d->hasLower || !d->hasUpper;
            }
            const auto previous = selected.find(id);
            // Equal SAT literals can name several predicates. Any one is a
            // valid premise for that literal. Prefer a complete footprint.
            if (previous == selected.end() || unbounded < previous->second.unbounded ||
                (unbounded == previous->second.unbounded &&
                 variables.size() < previous->second.variables.size()))
                selected.insert_or_assign(id, Source{&fact, std::move(variables), unbounded});
        }
        if (!failedKeys.empty() && selected.size() == failedKeys.size()) {
            std::unordered_set<std::string> variables;
            std::vector<NormalizedNiaConstraint> premises;
            a.complete = true;
            for (const auto& [id, source] : selected) {
                (void)id;
                if (!source.fact->domainVariable)
                    premises.push_back(cs[source.fact->constraint]);
                for (const auto& variable : source.variables) {
                    variables.insert(variable);
                    const auto* d = domains.getDomain(variable);
                    if (!d || !d->hasLower || !d->hasUpper) a.complete = false;
                }
            }
            if (a.complete) a.conflict = buildCompleteConflict(premises, domains, &variables);
            else for (const auto& variable : variables) {
                const auto* d = domains.getDomain(variable);
                if (!d || !d->hasLower || !d->hasUpper) a.refine.push_back(variable);
            }
            std::sort(a.refine.begin(), a.refine.end());
            if (bbProf) std::cerr << "[BB-CORE] facts=" << facts.size()
                << " selected=" << selected.size() << " variables=" << variables.size()
                << " unbounded=" << a.refine.size() << " complete=" << a.complete << '\n';
        } else if (full && !enc.overflowed() && plan.boxIsComplete) {
            // A backend without a usable assumption core retains the original
            // complete-box path, with every source/domain justification.
            a.complete = true;
            a.conflict = buildCompleteConflict(cs, domains);
        }
        if (enc.overflowed() && !a.complete) a.kind = Attempt::Overflow;
        return a;
    }
    if (enc.overflowed()) a.kind = Attempt::Overflow;
    if (bbDiag) std::cerr << "[BB-DIAG] SAT-solver-UNKNOWN@vars=" << enc.varCount() << "\n";
    return a;   // SAT solver Unknown
}

std::string BitBlastSolver::queryKey(const std::vector<NormalizedNiaConstraint>& cs,
                                     const DomainStore& domains) {
    // Length-prefix every field: variable names may contain any delimiter.
    // PolyIds identify immutable polynomials in this solver's kernel. Preserve
    // constraint/reason order; permutations may miss the cache but cannot alias.
    std::string key;
    const auto field = [&](const std::string& value) {
        key += std::to_string(value.size());
        key += ':';
        key += value;
    };
    const auto number = [&](auto value) { field(std::to_string(value)); };
    const auto literal = [&](SatLit lit) { number(lit.var); number(lit.sign); };
    const auto reasons = [&](const std::vector<SatLit>& lits) {
        number(lits.size());
        for (SatLit lit : lits) literal(lit);
    };
    const auto bound = [&](bool present, const BoundWithReason& b) {
        number(present);
        if (present) { field(b.value.get_str()); reasons(b.reasons); }
    };
    number(cs.size());
    for (const auto& c : cs) {
        number(static_cast<unsigned>(c.poly));
        number(static_cast<int>(c.rel));
        literal(c.reason);
    }
    number(domains.getAllDomains().size());
    for (const auto& entry : domains.getAllDomains()) {
        field(entry.first);
        const IntDomain& d = entry.second;
        bound(d.hasLower, d.lower);
        bound(d.hasUpper, d.upper);
        number(d.finiteValues.has_value());
        if (d.finiteValues) {
            number(d.finiteValues->size());
            for (const auto& value : *d.finiteValues) field(value.get_str());
            reasons(d.finiteSetReasons);
        }
        number(d.excludedValues.size());
        for (const auto& exclusion : d.excludedValues) {
            field(exclusion.first.get_str());
            reasons(exclusion.second);
        }
    }
    return key;
}

BitBlastResult BitBlastSolver::solve(const std::vector<NormalizedNiaConstraint>& cs,
                                     const DomainStore& domains,
                                     const IntegerModelValidator& validator) {
    BitBlastResult out;
    if (cs.empty() || !applicable(cs)) return out;   // Unknown

    std::string key = queryKey(cs, domains);
    if (lastResult_ && lastResult_->key == key) return lastResult_->result;
    lastResult_.reset();

    auto compute = [&]() -> BitBlastResult {
        BitBlastResult result;
        if (maxIters_ == 0 || maxBW_ == 0) return result;
        BitWidthPlan plan = estimator_.estimate(cs, domains);
        if (plan.width.empty()) return result;

        std::vector<std::string> unbounded;
        for (const auto& entry : plan.width) {
            const IntDomain* d = domains.getDomain(entry.first);
            if (d && d->hasLower && d->hasUpper) {
                // Never narrow a hard domain while still claiming completeness.
                // The exact required width must fit the encoding resource cap.
                if (entry.second > maxBW_) return result;
            } else {
                unbounded.push_back(entry.first);
            }
        }
        for (const auto& v : unbounded) plan.width[v] = std::min(2u, maxBW_);
        for (unsigned iter = 0; iter < maxIters_; ++iter) {
            if (wall::hasDeadline() && wall::remainingMs() == 0) return result;
            Attempt attempt = attemptAtWidths(plan, cs, domains, validator);
            if (attempt.kind == Attempt::Sat) {
                result.status = BitBlastResult::Status::Sat;
                result.model = std::move(attempt.model);
                return result;
            }
            if (attempt.complete) {
                if (attempt.conflict) {
                    result.status = BitBlastResult::Status::UnsatComplete;
                    result.conflict = std::move(attempt.conflict);
                }
                return result;
            }
            if (plan.boxIsComplete || attempt.kind == Attempt::Overflow) return result;
            const auto& refine = attempt.refine.empty() ? unbounded : attempt.refine;
            bool changed = false;
            for (const auto& v : refine) {
                auto& width = plan.width.at(v);
                if (width == maxBW_) continue;
                width = width > maxBW_ / 2 ? maxBW_ : width * 2;
                changed = true;
            }
            if (!changed) break;
        }
        return result; // Artificial bounds never justify an integer conflict.
    };

    BitBlastResult r = compute();
    if (r.status != BitBlastResult::Status::Unknown)
        lastResult_ = CachedResult{std::move(key), r};
    return r;
}

} // namespace xolver::bitblast
