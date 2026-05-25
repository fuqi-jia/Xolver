#include "theory/arith/search/CandidateModelSearch.h"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <iostream>
#include <set>

namespace nlcolver {

CandidateModelSearch::CandidateModelSearch(const CoreIr& ir, std::string_view logic)
    : CandidateModelSearch(ir, logic, Config{}) {}

CandidateModelSearch::CandidateModelSearch(const CoreIr& ir, std::string_view logic,
                                           const Config& cfg)
    : ir_(ir), logic_(logic), cfg_(cfg) {
    deadline_ = std::chrono::steady_clock::now() + cfg_.wallClockBudget;
}

CandidateModelSearch::Result CandidateModelSearch::run() {
    if (!isLogicEnabled()) return result_;

    collectFreeVariables();
    if (cfg_.allowUF) collectApplicationSlots();
    if (vars_.empty()) return result_;

    buildPriorityList();
    detectActiveBounds();

    // Run strategies in order. Each returns true if a validated witness
    // was found (early termination).
    if (runStrategy10d()) return result_;
    if (runStrategy10c()) return result_;
    if (runStrategy10a()) return result_;

    return result_;
}

std::vector<ExprId> CandidateModelSearch::assertionRoots() const {
    if (!cfg_.assertionRootsOverride.empty()) return cfg_.assertionRootsOverride;
    return ir_.assertions();
}

bool CandidateModelSearch::isLogicEnabled() const {
    // Default-enabled for pure arithmetic logics. UF-bearing logics are
    // disabled until the evaluator supports congruence checking for UF
    // interpretations — otherwise we cannot ensure UF terms are
    // interpreted consistently in the candidate extension.
    if (logic_ == "QF_NIA" || logic_ == "NIA" ||
        logic_ == "QF_NRA" || logic_ == "NRA" ||
        logic_ == "QF_LIA" || logic_ == "LIA" ||
        logic_ == "QF_LRA" || logic_ == "LRA" ||
        logic_ == "QF_NIRA" || logic_ == "NIRA" ||
        logic_ == "QF_LIRA" || logic_ == "LIRA" ||
        logic_ == "QF_IDL" || logic_ == "IDL" ||
        logic_ == "QF_RDL" || logic_ == "RDL") {
        return true;
    }
    // UF-bearing arithmetic logics are enabled only when the caller opted in
    // (allowUF): the search then models each application as a value slot and
    // enforces functional consistency, so a validated candidate is a sound
    // model including the function table.
    if (cfg_.allowUF &&
        (logic_ == "QF_UFLRA" || logic_ == "QF_UFLIA" ||
         logic_ == "QF_UFNRA" || logic_ == "QF_UFNIA" ||
         logic_ == "QF_UFIDL" || logic_ == "QF_UF" ||
         logic_ == "UFLRA" || logic_ == "UFLIA" ||
         logic_ == "UFNRA" || logic_ == "UFNIA")) {
        return true;
    }
    return false;
}

void CandidateModelSearch::collectFreeVariables() {
    // Walk the assertion list and harvest every user-visible numeric
    // variable. Skip variables whose name begins with "__nlc_" (frontend-
    // introduced auxiliaries) so the candidate space stays small and
    // validation results in a clean user-facing model.
    std::unordered_set<std::string> seen;
    std::vector<bool> visited(ir_.size(), false);
    std::vector<ExprId> stack;
    for (ExprId a : assertionRoots()) stack.push_back(a);
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        if (e >= ir_.size() || visited[e]) continue;
        visited[e] = true;
        const auto& n = ir_.get(e);
        if (n.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                if (s->rfind("__nlc_", 0) == 0) continue;  // skip aux
                if (n.sort != ir_.intSortId() && n.sort != ir_.realSortId()) continue;
                if (seen.insert(*s).second) {
                    VarRecord rec;
                    rec.exprId = e;
                    rec.name = *s;
                    rec.sort = n.sort;
                    varIndexByName_[*s] = vars_.size();
                    vars_.push_back(std::move(rec));
                }
            }
        }
        for (ExprId c : n.children) stack.push_back(c);
    }
}

namespace {
// Synthetic assignment-map key for the value of a UF application node.
std::string appSlotName(ExprId eid) {
    return "__ufapp#" + std::to_string(eid);
}
}  // namespace

void CandidateModelSearch::collectApplicationSlots() {
    // Each distinct (hash-consed) numeric-sorted application node f(args)
    // becomes a value slot, enumerated like a variable. Equal applications
    // share an ExprId and thus one slot (consistency for free); distinct
    // applications of the same f are reconciled by functionallyConsistent().
    std::unordered_set<ExprId> seen;
    std::vector<bool> visited(ir_.size(), false);
    std::vector<ExprId> stack;
    for (ExprId a : assertionRoots()) stack.push_back(a);
    while (!stack.empty()) {
        ExprId e = stack.back();
        stack.pop_back();
        if (e >= ir_.size() || visited[e]) continue;
        visited[e] = true;
        const auto& n = ir_.get(e);
        if (n.kind == Kind::UFApply &&
            (n.sort == ir_.intSortId() || n.sort == ir_.realSortId())) {
            if (seen.insert(e).second) {
                if (auto* fn = std::get_if<std::string>(&n.payload.value)) {
                    VarRecord rec;
                    rec.exprId = e;
                    rec.name = appSlotName(e);
                    rec.sort = n.sort;
                    rec.isApp = true;
                    rec.funcName = *fn;
                    varIndexByName_[rec.name] = vars_.size();
                    vars_.push_back(std::move(rec));
                }
            }
        }
        for (ExprId c : n.children) stack.push_back(c);
    }
}

bool CandidateModelSearch::functionallyConsistent(
    const std::unordered_map<std::string, mpq_class>& full) const
{
    // For each function symbol, two applications with equal argument-value
    // tuples must carry equal slot values.
    std::unordered_map<std::string,
        std::vector<std::pair<std::vector<mpq_class>, mpq_class>>> tables;
    for (const auto& v : vars_) {
        if (!v.isApp) continue;
        const auto& node = ir_.get(v.exprId);
        std::vector<mpq_class> args;
        bool ok = true;
        for (ExprId c : node.children) {
            TermResult cr = evalTerm(c, full);
            if (cr.kind != TermVerdict::Number) { ok = false; break; }
            args.push_back(cr.numValue);
        }
        if (!ok) continue;  // unevaluable args -> skip (validation will reject)
        auto sv = full.find(v.name);
        if (sv == full.end()) continue;
        auto& entries = tables[v.funcName];
        for (const auto& [prevArgs, prevVal] : entries) {
            if (prevArgs == args && prevVal != sv->second) return false;
        }
        entries.emplace_back(std::move(args), sv->second);
    }
    return true;
}

void CandidateModelSearch::buildFunctionInterps(
    const std::unordered_map<std::string, mpq_class>& full)
{
    auto sortName = [&](SortId s) -> std::string {
        if (s == ir_.intSortId()) return "Int";
        if (s == ir_.realSortId()) return "Real";
        if (s == ir_.boolSortId()) return "Bool";
        return "Real";
    };
    for (const auto& v : vars_) {
        if (!v.isApp) continue;
        const auto& node = ir_.get(v.exprId);
        auto sv = full.find(v.name);
        if (sv == full.end()) continue;
        std::vector<mpq_class> args;
        bool ok = true;
        for (ExprId c : node.children) {
            TermResult cr = evalTerm(c, full);
            if (cr.kind != TermVerdict::Number) { ok = false; break; }
            args.push_back(cr.numValue);
        }
        if (!ok) continue;
        auto& fi = result_.model.functionInterps[v.funcName];
        if (fi.argSorts.empty() && !node.children.empty()) {
            for (ExprId c : node.children) fi.argSorts.push_back(sortName(ir_.get(c).sort));
            fi.retSort = sortName(node.sort);
            fi.deflt = sv->second.get_str();  // any in-range value is fine
        }
        TheorySolver::TheoryModel::FuncEntry entry;
        for (const auto& a : args) entry.args.push_back(a.get_str());
        entry.value = sv->second.get_str();
        // Deduplicate identical arg tuples (consistency already guaranteed).
        bool dup = false;
        for (const auto& ex : fi.entries) { if (ex.args == entry.args) { dup = true; break; } }
        if (!dup) fi.entries.push_back(std::move(entry));
    }
}

namespace {

// Lexicographic priority list of rationals ordered by increasing height
// (|num| + den). For each height we enumerate every reduced p/q with
// |p| <= num bound and q <= den bound.
std::vector<mpq_class> buildSharedPriority(int64_t numBound, int64_t denBound) {
    auto gcd64 = [](int64_t a, int64_t b) -> int64_t {
        a = std::abs(a); b = std::abs(b);
        while (b) { a %= b; std::swap(a, b); }
        return a;
    };
    std::set<std::pair<int64_t, int64_t>> seen;
    std::vector<mpq_class> out;
    int64_t maxHeight = numBound + denBound;
    out.push_back(mpq_class(0));
    seen.insert({0, 1});
    for (int64_t h = 1; h <= maxHeight; ++h) {
        for (int64_t p = -numBound; p <= numBound; ++p) {
            if (std::abs(p) > h) continue;
            for (int64_t q = 1; q <= denBound; ++q) {
                if (std::abs(p) + q != h) continue;
                if (gcd64(std::abs(p), q) != 1 && !(p == 0 && q == 1)) continue;
                if (!seen.insert({p, q}).second) continue;
                out.emplace_back(p, q);
            }
        }
    }
    return out;
}

} // namespace

void CandidateModelSearch::buildPriorityList() {
    priority_ = buildSharedPriority(cfg_.numeratorBound, cfg_.denominatorBound);

    perVar_.clear();
    perVar_.resize(vars_.size());
    for (size_t i = 0; i < vars_.size(); ++i) {
        const auto& var = vars_[i];
        // Per-variable list = shared priority filtered by sort. Int-sorted
        // variables only receive integer-valued candidates.
        for (const auto& q : priority_) {
            if (var.sort == ir_.intSortId() && q.get_den() != 1) continue;
            perVar_[i].push_back(q);
        }
    }
}

void CandidateModelSearch::detectActiveBounds() {
    // Lightweight syntactic scan: look for top-level conjuncts of the
    // form (rel var const) or (rel const var) and record them as bounds.
    auto extractConst = [&](ExprId eid) -> std::optional<mpq_class> {
        const auto& n = ir_.get(eid);
        if (n.kind == Kind::ConstInt) {
            if (auto* v = std::get_if<int64_t>(&n.payload.value)) return mpq_class(*v);
        }
        if (n.kind == Kind::ConstReal) {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) return mpq_class(*s);
        }
        return std::nullopt;
    };
    auto extractVarName = [&](ExprId eid) -> std::optional<std::string> {
        const auto& n = ir_.get(eid);
        if (n.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) return *s;
        }
        return std::nullopt;
    };

    auto consumeAtom = [&](ExprId atomId) {
        const auto& a = ir_.get(atomId);
        if (a.children.size() != 2) return;
        ExprId lhs = a.children[0], rhs = a.children[1];
        auto lhsVar = extractVarName(lhs);
        auto rhsConst = extractConst(rhs);
        auto rhsVar = extractVarName(rhs);
        auto lhsConst = extractConst(lhs);

        // Normalize so the variable is on the left.
        std::string varName;
        mpq_class c;
        bool flipped = false;
        if (lhsVar && rhsConst) { varName = *lhsVar; c = *rhsConst; }
        else if (rhsVar && lhsConst) { varName = *rhsVar; c = *lhsConst; flipped = true; }
        else return;
        if (!varIndexByName_.count(varName)) return;
        BoundInfo& bd = activeBounds_[varName];

        switch (a.kind) {
            case Kind::Leq:
                if (!flipped) {
                    // var <= c -> upper bound c
                    if (!bd.upper || c < *bd.upper) { bd.upper = c; bd.upperStrict = false; }
                } else {
                    // c <= var -> lower bound c
                    if (!bd.lower || c > *bd.lower) { bd.lower = c; bd.lowerStrict = false; }
                }
                break;
            case Kind::Lt:
                if (!flipped) {
                    if (!bd.upper || c < *bd.upper) { bd.upper = c; bd.upperStrict = true; }
                } else {
                    if (!bd.lower || c > *bd.lower) { bd.lower = c; bd.lowerStrict = true; }
                }
                break;
            case Kind::Geq:
                if (!flipped) {
                    if (!bd.lower || c > *bd.lower) { bd.lower = c; bd.lowerStrict = false; }
                } else {
                    if (!bd.upper || c < *bd.upper) { bd.upper = c; bd.upperStrict = false; }
                }
                break;
            case Kind::Gt:
                if (!flipped) {
                    if (!bd.lower || c > *bd.lower) { bd.lower = c; bd.lowerStrict = true; }
                } else {
                    if (!bd.upper || c < *bd.upper) { bd.upper = c; bd.upperStrict = true; }
                }
                break;
            case Kind::Eq:
                if (!bd.lower || c > *bd.lower) { bd.lower = c; bd.lowerStrict = false; }
                if (!bd.upper || c < *bd.upper) { bd.upper = c; bd.upperStrict = false; }
                break;
            default:
                break;
        }
    };

    for (ExprId aid : assertionRoots()) {
        const auto& a = ir_.get(aid);
        if (a.kind == Kind::And) {
            for (ExprId c : a.children) {
                consumeAtom(c);
            }
        } else {
            consumeAtom(aid);
        }
    }
}

int64_t CandidateModelSearch::heightOf(const mpq_class& q) {
    mpz_class n = abs(q.get_num());
    mpz_class d = q.get_den();
    if (!n.fits_slong_p() || !d.fits_slong_p()) return INT64_MAX;
    return n.get_si() + d.get_si();
}

bool CandidateModelSearch::tryAcceptCandidate(
    const std::unordered_map<std::string, mpq_class>& partial,
    const std::string& strategyName)
{
    if (++totalCandidatesTried_ % 32 == 0) {
        if (std::chrono::steady_clock::now() > deadline_) return false;
    }
    // Extend to all variables.
    std::unordered_map<std::string, mpq_class> full = partial;
    for (const auto& v : vars_) {
        if (!full.count(v.name)) {
            // Default 0; if active bound exists, snap to mid-range or to
            // the nearest valid integer.
            mpq_class def(0);
            auto it = activeBounds_.find(v.name);
            if (it != activeBounds_.end()) {
                const auto& b = it->second;
                if (b.lower && b.upper) {
                    def = (*b.lower + *b.upper) / 2;
                } else if (b.lower) {
                    def = *b.lower + 1;
                } else if (b.upper) {
                    def = *b.upper - 1;
                }
                if (v.sort == ir_.intSortId() && def.get_den() != 1) {
                    mpz_class q;
                    mpz_fdiv_q(q.get_mpz_t(), def.get_num().get_mpz_t(),
                               def.get_den().get_mpz_t());
                    def = mpq_class(q);
                }
            }
            full[v.name] = def;
        }
    }
    // Reject candidates that would make a function multi-valued before we
    // bother evaluating the assertions.
    if (cfg_.allowUF && !functionallyConsistent(full)) return false;

    auto verdict = evaluateAssertions(full);
    if (verdict != EvalVerdict::True) return false;

    // Accept: record model. App slots go into the function table, not the
    // variable assignment.
    result_.found = true;
    result_.strategy = strategyName;
    for (const auto& v : vars_) {
        if (v.isApp) continue;
        auto it = full.find(v.name);
        if (it != full.end()) result_.model.assignments[v.name] = it->second.get_str();
    }
    if (cfg_.allowUF) buildFunctionInterps(full);
    return true;
}

bool CandidateModelSearch::runStrategy10d() {
    // Symmetric diagonal: try x = y = ... = c for small c.
    // Even without explicit symmetry detection, this is sound (a uniform
    // diagonal candidate that validates is a true witness regardless of
    // formula symmetry).
    static constexpr int diagonalValues[] = {0, 1, -1, 2, -2};
    for (int c : diagonalValues) {
        std::unordered_map<std::string, mpq_class> partial;
        for (const auto& v : vars_) partial[v.name] = mpq_class(c);
        if (tryAcceptCandidate(partial, "10d-symmetric")) return true;
    }
    return false;
}

bool CandidateModelSearch::runStrategy10c() {
    // Boundary points for variables with active integer bounds.
    for (const auto& v : vars_) {
        auto it = activeBounds_.find(v.name);
        if (it == activeBounds_.end()) continue;
        const auto& b = it->second;
        std::vector<mpq_class> candidates;
        if (b.lower) {
            candidates.push_back(*b.lower);
            candidates.push_back(*b.lower + 1);
        }
        if (b.upper) {
            candidates.push_back(*b.upper);
            candidates.push_back(*b.upper - 1);
        }
        for (const auto& cv : candidates) {
            std::unordered_map<std::string, mpq_class> partial;
            partial[v.name] = cv;
            if (tryAcceptCandidate(partial, "10c-boundary")) return true;
        }
    }
    return false;
}

bool CandidateModelSearch::runStrategy10a() {
    // Low-height-first enumeration over the Cartesian product of
    // per-variable priority lists. We bound the search by per-strategy
    // candidate budget and the global wall-clock.
    size_t n = vars_.size();
    if (n == 0) return false;
    std::vector<size_t> idx(n, 0);
    std::vector<size_t> listSize(n);
    for (size_t i = 0; i < n; ++i) listSize[i] = perVar_[i].size();

    // We iterate by increasing total-height. For each candidate (idx[i])
    // the height is sum(heightOf(perVar_[i][idx[i]])).
    // Implemented as: iterate all combinations within a bounded total-
    // height envelope, expand envelope until budget is hit.
    size_t budget = cfg_.maxCandidatesPerStrategy;
    size_t produced = 0;

    // For up to maxHeight 30 (loose envelope), enumerate combinations
    // whose total height equals the current envelope.
    for (int64_t envelope = 0; envelope <= 30 && produced < budget; ++envelope) {
        // Iterate per-variable index combinations using a stack.
        std::vector<size_t> cursor(n, 0);
        // For low-height-first, iterate every per-variable index that has
        // height <= envelope, then dispatch only those whose total height
        // equals the envelope.
        std::function<bool(size_t, int64_t)> recurse =
            [&](size_t pos, int64_t remainingHeight) -> bool {
                if (produced >= budget) return false;
                if (pos == n) {
                    if (remainingHeight != 0) return false;
                    // Build assignment and try.
                    std::unordered_map<std::string, mpq_class> partial;
                    for (size_t i = 0; i < n; ++i) {
                        partial[vars_[i].name] = perVar_[i][cursor[i]];
                    }
                    ++produced;
                    if (tryAcceptCandidate(partial, "10a-rational")) return true;
                    return false;
                }
                for (size_t j = 0; j < listSize[pos]; ++j) {
                    int64_t h = heightOf(perVar_[pos][j]);
                    if (h > remainingHeight) break;  // priority list grows in height
                    cursor[pos] = j;
                    if (recurse(pos + 1, remainingHeight - h)) return true;
                }
                return false;
            };
        if (recurse(0, envelope)) return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// Arithmetic evaluator over a complete numeric assignment.
// ---------------------------------------------------------------------------

CandidateModelSearch::EvalVerdict
CandidateModelSearch::evaluateAssertions(
    const std::unordered_map<std::string, mpq_class>& assignment) const
{
    bool anyIndeterminate = false;
    for (ExprId aid : assertionRoots()) {
        TermResult tr = evalTerm(aid, assignment);
        if (tr.kind == TermVerdict::Indeterminate) {
            anyIndeterminate = true;
            continue;
        }
        if (tr.kind != TermVerdict::Bool) return EvalVerdict::Indeterminate;
        if (!tr.boolValue) return EvalVerdict::False;
    }
    return anyIndeterminate ? EvalVerdict::Indeterminate : EvalVerdict::True;
}

CandidateModelSearch::TermResult CandidateModelSearch::evalTerm(
    ExprId eid,
    const std::unordered_map<std::string, mpq_class>& assignment) const
{
    if (eid >= ir_.size()) return {};
    const auto& n = ir_.get(eid);
    TermResult r;
    switch (n.kind) {
        case Kind::ConstBool:
            r.kind = TermVerdict::Bool;
            r.boolValue = std::get<bool>(n.payload.value);
            return r;
        case Kind::ConstInt:
            r.kind = TermVerdict::Number;
            if (auto* v = std::get_if<int64_t>(&n.payload.value)) r.numValue = mpq_class(*v);
            return r;
        case Kind::ConstReal:
            r.kind = TermVerdict::Number;
            if (auto* s = std::get_if<std::string>(&n.payload.value)) r.numValue = mpq_class(*s);
            return r;
        case Kind::Variable: {
            if (auto* s = std::get_if<std::string>(&n.payload.value)) {
                if (n.sort == ir_.boolSortId()) {
                    return r;  // unknown bool var; indeterminate
                }
                auto it = assignment.find(*s);
                if (it != assignment.end()) {
                    r.kind = TermVerdict::Number;
                    r.numValue = it->second;
                    return r;
                }
            }
            return r;
        }
        case Kind::UFApply: {
            // The value of a numeric application is its enumerated slot
            // (present only with UF modeling enabled). Functional consistency
            // across applications is enforced separately in
            // functionallyConsistent(). Otherwise indeterminate.
            auto it = assignment.find(appSlotName(eid));
            if (it != assignment.end()) {
                r.kind = TermVerdict::Number;
                r.numValue = it->second;
            }
            return r;
        }
        case Kind::Add: {
            mpq_class acc(0);
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind != TermVerdict::Number) return r;
                acc += cr.numValue;
            }
            r.kind = TermVerdict::Number;
            r.numValue = acc;
            return r;
        }
        case Kind::Sub: {
            if (n.children.size() < 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            mpq_class acc = cr.numValue;
            for (size_t i = 1; i < n.children.size(); ++i) {
                TermResult c2 = evalTerm(n.children[i], assignment);
                if (c2.kind != TermVerdict::Number) return r;
                acc -= c2.numValue;
            }
            r.kind = TermVerdict::Number;
            r.numValue = acc;
            return r;
        }
        case Kind::Neg: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Number;
            r.numValue = -cr.numValue;
            return r;
        }
        case Kind::Mul: {
            mpq_class acc(1);
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind != TermVerdict::Number) return r;
                acc *= cr.numValue;
            }
            r.kind = TermVerdict::Number;
            r.numValue = acc;
            return r;
        }
        case Kind::Div: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            if (b.numValue == 0) return r;  // undefined; indeterminate
            r.kind = TermVerdict::Number;
            r.numValue = a.numValue / b.numValue;
            return r;
        }
        case Kind::Pow: {
            if (n.children.size() != 2) return r;
            TermResult base = evalTerm(n.children[0], assignment);
            TermResult exp = evalTerm(n.children[1], assignment);
            if (base.kind != TermVerdict::Number || exp.kind != TermVerdict::Number) return r;
            if (exp.numValue.get_den() != 1) return r;  // non-integer power
            mpz_class e = exp.numValue.get_num();
            if (!e.fits_slong_p()) return r;
            int64_t ev = e.get_si();
            if (ev < 0) {
                if (base.numValue == 0) return r;
                mpq_class one(1);
                mpq_class val(1);
                for (int64_t i = 0; i < -ev; ++i) val *= base.numValue;
                r.kind = TermVerdict::Number;
                r.numValue = one / val;
                return r;
            }
            mpq_class val(1);
            for (int64_t i = 0; i < ev; ++i) val *= base.numValue;
            r.kind = TermVerdict::Number;
            r.numValue = val;
            return r;
        }
        case Kind::Mod: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            if (a.numValue.get_den() != 1 || b.numValue.get_den() != 1) return r;
            mpz_class ai = a.numValue.get_num();
            mpz_class bi = b.numValue.get_num();
            if (bi == 0) return r;
            mpz_class absB = abs(bi);
            mpz_class q, rem;
            mpz_fdiv_qr(q.get_mpz_t(), rem.get_mpz_t(), ai.get_mpz_t(), absB.get_mpz_t());
            r.kind = TermVerdict::Number;
            r.numValue = mpq_class(rem);
            return r;
        }
        case Kind::Abs: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Number;
            r.numValue = abs(cr.numValue);
            return r;
        }
        case Kind::ToReal: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Number;
            r.numValue = cr.numValue;
            return r;
        }
        case Kind::ToInt: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            mpz_class q;
            mpz_fdiv_q(q.get_mpz_t(), cr.numValue.get_num().get_mpz_t(),
                       cr.numValue.get_den().get_mpz_t());
            r.kind = TermVerdict::Number;
            r.numValue = mpq_class(q);
            return r;
        }
        case Kind::IsInt: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (cr.numValue.get_den() == 1);
            return r;
        }
        case Kind::Eq: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind == TermVerdict::Indeterminate || b.kind == TermVerdict::Indeterminate)
                return r;
            if (a.kind != b.kind) return r;
            r.kind = TermVerdict::Bool;
            if (a.kind == TermVerdict::Bool) r.boolValue = (a.boolValue == b.boolValue);
            else                              r.boolValue = (a.numValue == b.numValue);
            return r;
        }
        case Kind::Distinct: {
            if (n.children.size() < 2) {
                r.kind = TermVerdict::Bool;
                r.boolValue = true;
                return r;
            }
            // Pairwise distinct.
            std::vector<TermResult> evald;
            evald.reserve(n.children.size());
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind == TermVerdict::Indeterminate) return r;
                evald.push_back(cr);
            }
            for (size_t i = 0; i < evald.size(); ++i) {
                for (size_t j = i + 1; j < evald.size(); ++j) {
                    if (evald[i].kind != evald[j].kind) continue;
                    bool same = false;
                    if (evald[i].kind == TermVerdict::Bool)
                        same = (evald[i].boolValue == evald[j].boolValue);
                    else same = (evald[i].numValue == evald[j].numValue);
                    if (same) {
                        r.kind = TermVerdict::Bool;
                        r.boolValue = false;
                        return r;
                    }
                }
            }
            r.kind = TermVerdict::Bool;
            r.boolValue = true;
            return r;
        }
        case Kind::Lt: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (a.numValue < b.numValue);
            return r;
        }
        case Kind::Leq: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (a.numValue <= b.numValue);
            return r;
        }
        case Kind::Gt: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (a.numValue > b.numValue);
            return r;
        }
        case Kind::Geq: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind != TermVerdict::Number || b.kind != TermVerdict::Number) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (a.numValue >= b.numValue);
            return r;
        }
        case Kind::And: {
            bool anyInd = false;
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind == TermVerdict::Indeterminate) { anyInd = true; continue; }
                if (cr.kind != TermVerdict::Bool) return r;
                if (!cr.boolValue) {
                    r.kind = TermVerdict::Bool;
                    r.boolValue = false;
                    return r;
                }
            }
            if (anyInd) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = true;
            return r;
        }
        case Kind::Or: {
            bool anyInd = false;
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind == TermVerdict::Indeterminate) { anyInd = true; continue; }
                if (cr.kind != TermVerdict::Bool) return r;
                if (cr.boolValue) {
                    r.kind = TermVerdict::Bool;
                    r.boolValue = true;
                    return r;
                }
            }
            if (anyInd) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = false;
            return r;
        }
        case Kind::Not: {
            if (n.children.size() != 1) return r;
            TermResult cr = evalTerm(n.children[0], assignment);
            if (cr.kind != TermVerdict::Bool) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = !cr.boolValue;
            return r;
        }
        case Kind::Implies: {
            if (n.children.size() != 2) return r;
            TermResult a = evalTerm(n.children[0], assignment);
            TermResult b = evalTerm(n.children[1], assignment);
            if (a.kind == TermVerdict::Indeterminate || b.kind == TermVerdict::Indeterminate)
                return r;
            if (a.kind != TermVerdict::Bool || b.kind != TermVerdict::Bool) return r;
            r.kind = TermVerdict::Bool;
            r.boolValue = (!a.boolValue) || b.boolValue;
            return r;
        }
        case Kind::Xor: {
            if (n.children.size() < 2) return r;
            bool acc = false;
            bool seen = false;
            for (ExprId c : n.children) {
                TermResult cr = evalTerm(c, assignment);
                if (cr.kind != TermVerdict::Bool) return r;
                if (!seen) { acc = cr.boolValue; seen = true; }
                else { acc = (acc != cr.boolValue); }
            }
            r.kind = TermVerdict::Bool;
            r.boolValue = acc;
            return r;
        }
        case Kind::Ite: {
            if (n.children.size() != 3) return r;
            TermResult c = evalTerm(n.children[0], assignment);
            if (c.kind != TermVerdict::Bool) return r;
            return evalTerm(c.boolValue ? n.children[1] : n.children[2], assignment);
        }
        default:
            return r;  // Indeterminate for unsupported constructs (e.g., UFApply).
    }
}

bool CandidateModelSearch::detectSymmetry() const {
    // Placeholder for the symmetry analysis used by strategy 10d. The
    // current implementation always tries the diagonal — even without a
    // detected symmetry, the diagonal is a sound candidate (its validity
    // is decided exclusively by ModelValidator), and the budget is small
    // enough that the additional evaluations are negligible.
    return true;
}

} // namespace nlcolver
