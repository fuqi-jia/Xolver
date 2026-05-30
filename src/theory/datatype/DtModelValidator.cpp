#include "theory/datatype/DtModelValidator.h"
#include <variant>
#include <cstring>
#include <iostream>
#include <cstdlib>

namespace xolver {

namespace {
constexpr char kCtorPrefix[] = "#dt.ctor.";
constexpr char kSelPrefix[]  = "#dt.sel.";
constexpr char kTesterPrefix[] = "#dt.is.";
}  // namespace

std::string DtModelValidator::stripDtPrefix(const std::string& sym) {
    if (sym.rfind(kCtorPrefix, 0) == 0)   return sym.substr(sizeof(kCtorPrefix) - 1);
    if (sym.rfind(kSelPrefix, 0) == 0)    return sym.substr(sizeof(kSelPrefix) - 1);
    if (sym.rfind(kTesterPrefix, 0) == 0) return sym.substr(sizeof(kTesterPrefix) - 1);
    return std::string();
}

std::string DtModelValidator::constructorOfClass(EClassId c) const {
    for (EufTermId m : egraph_.classMembers(c)) {
        const std::string& sym = tm_.symbolName(tm_.node(m).symbol);
        if (sym.rfind(kCtorPrefix, 0) == 0) {
            return sym.substr(sizeof(kCtorPrefix) - 1);
        }
    }
    return std::string();
}

EufTermId DtModelValidator::constructorTermInClass(EClassId c,
                                                   const std::string& ctorName) const {
    const std::string target = std::string(kCtorPrefix) + ctorName;
    for (EufTermId m : egraph_.classMembers(c)) {
        const std::string& sym = tm_.symbolName(tm_.node(m).symbol);
        if (sym == target) return m;
    }
    return NullEufTerm;
}

SortId DtModelValidator::classDatatypeSort(EClassId c) const {
    for (EufTermId m : egraph_.classMembers(c)) {
        ExprId e = tm_.node(m).origin;
        if (e == NullExpr || e >= static_cast<ExprId>(ir_.size())) continue;
        SortId s = ir_.get(e).sort;
        if (dts_.isDatatypeSort(s)) return s;
    }
    return NullSort;
}

DtModelValidator::R DtModelValidator::eval(ExprId e) {
    auto memoIt = memo_.find(e);
    if (memoIt != memo_.end()) return memoIt->second;

    auto store = [&](R r) -> R {
        memo_[e] = r;
        return r;
    };
    auto indeterminate = [&]() -> R {
        R r; r.kind = Kind3::Indeterminate; return store(r);
    };
    auto boolR = [&](bool v) -> R {
        R r; r.kind = Kind3::Bool; r.b = v; return store(r);
    };

    if (e == NullExpr) return indeterminate();
    if (e >= static_cast<ExprId>(ir_.size())) return indeterminate();
    const CoreExpr& n = ir_.get(e);

    switch (n.kind) {
        case Kind::ConstBool: {
            R r; r.kind = Kind3::Bool;
            r.b = std::get<bool>(n.payload.value);
            return store(r);
        }
        case Kind::ConstInt: {
            R r; r.kind = Kind3::Number;
            r.numStr = mpq_class(std::get<int64_t>(n.payload.value)).get_str();
            return store(r);
        }
        case Kind::ConstReal: {
            R r; r.kind = Kind3::Number;
            r.numStr = std::get<std::string>(n.payload.value);
            return store(r);
        }
        case Kind::Variable:
        case Kind::Constructor:
        case Kind::Selector:
        case Kind::UFApply: {
            // For all these, the value is the e-class of the interned term.
            // Boolean-sorted variables/applications: resolve via merge with
            // true/false sentinel if available (only meaningful when interned
            // and merged); else Indeterminate.
            EufTermId t = tm_.findTerm(e);
            if (t == NullEufTerm) return indeterminate();
            EClassId c = egraph_.rep(t);
            if (n.sort == ir_.boolSortId()) {
                // Resolve to true/false via the boolean sentinel classes.
                EufTermId trueT = tm_.trueConstant();
                EufTermId falseT = tm_.falseConstant();
                if (trueT != NullEufTerm && egraph_.same(t, trueT)) return boolR(true);
                if (falseT != NullEufTerm && egraph_.same(t, falseT)) return boolR(false);
                return indeterminate();
            }
            if (dts_.isDatatypeSort(n.sort)) {
                R r; r.kind = Kind3::DtClass; r.cls = c; return store(r);
            }
            // Numeric/other: opaque — store class only.
            R r; r.kind = Kind3::Indeterminate; r.cls = c; return store(r);
        }
        case Kind::Tester: {
            // is-C(x): True iff x's class has ctor C; False iff has some
            // OTHER ctor; Indeterminate iff no ctor in class.
            if (n.children.size() != 1) return indeterminate();
            R x = eval(n.children[0]);
            if (x.kind != Kind3::DtClass) return indeterminate();
            std::string ctorName = constructorOfClass(x.cls);
            if (ctorName.empty()) return indeterminate();
            // The tester payload name should match a constructor name (or
            // be "is-<C>"). Per DtReasoner.cpp pattern, both are accepted.
            const std::string* targetNm =
                std::get_if<std::string>(&n.payload.value);
            std::string target = targetNm ? *targetNm : std::string();
            if (target.rfind("is-", 0) == 0) target = target.substr(3);
            if (target.empty()) return indeterminate();
            return boolR(target == ctorName);
        }
        case Kind::Eq: {
            if (n.children.size() < 2) return boolR(true);
            R a = eval(n.children[0]);
            // For chained eq, just require all pairwise equal w.r.t. first.
            bool indet = false;
            for (size_t i = 1; i < n.children.size(); ++i) {
                R b = eval(n.children[i]);
                if (a.kind == Kind3::Bool && b.kind == Kind3::Bool) {
                    if (a.b != b.b) return boolR(false);
                } else if (a.kind == Kind3::DtClass && b.kind == Kind3::DtClass) {
                    if (a.cls == b.cls) continue;
                    // Different classes: definitively unequal iff each holds
                    // a distinct constructor.
                    std::string ca = constructorOfClass(a.cls);
                    std::string cb = constructorOfClass(b.cls);
                    if (!ca.empty() && !cb.empty() && ca != cb) return boolR(false);
                    indet = true;
                } else if (a.kind == Kind3::Number && b.kind == Kind3::Number) {
                    try {
                        if (mpq_class(a.numStr) != mpq_class(b.numStr)) return boolR(false);
                    } catch (...) { indet = true; }
                } else {
                    indet = true;
                }
            }
            if (indet) return indeterminate();
            return boolR(true);
        }
        case Kind::Distinct: {
            // distinct(a,b,...): all pairs must be definitively unequal.
            std::vector<R> vs;
            vs.reserve(n.children.size());
            for (ExprId c : n.children) vs.push_back(eval(c));
            bool indet = false;
            for (size_t i = 0; i < vs.size(); ++i) {
                for (size_t j = i + 1; j < vs.size(); ++j) {
                    if (vs[i].kind == Kind3::Bool && vs[j].kind == Kind3::Bool) {
                        if (vs[i].b == vs[j].b) return boolR(false);
                    } else if (vs[i].kind == Kind3::DtClass && vs[j].kind == Kind3::DtClass) {
                        if (vs[i].cls == vs[j].cls) return boolR(false);
                        std::string ca = constructorOfClass(vs[i].cls);
                        std::string cb = constructorOfClass(vs[j].cls);
                        if (ca.empty() || cb.empty() || ca == cb) indet = true;
                    } else if (vs[i].kind == Kind3::Number && vs[j].kind == Kind3::Number) {
                        try {
                            if (mpq_class(vs[i].numStr) == mpq_class(vs[j].numStr)) return boolR(false);
                        } catch (...) { indet = true; }
                    } else {
                        indet = true;
                    }
                }
            }
            if (indet) return indeterminate();
            return boolR(true);
        }
        case Kind::Not: {
            if (n.children.size() != 1) return indeterminate();
            R x = eval(n.children[0]);
            if (x.kind != Kind3::Bool) return indeterminate();
            return boolR(!x.b);
        }
        case Kind::And: {
            bool anyIndet = false;
            for (ExprId c : n.children) {
                R r = eval(c);
                if (r.kind == Kind3::Bool) {
                    if (!r.b) return boolR(false);
                } else {
                    anyIndet = true;
                }
            }
            if (anyIndet) return indeterminate();
            return boolR(true);
        }
        case Kind::Or: {
            bool anyIndet = false;
            for (ExprId c : n.children) {
                R r = eval(c);
                if (r.kind == Kind3::Bool) {
                    if (r.b) return boolR(true);
                } else {
                    anyIndet = true;
                }
            }
            if (anyIndet) return indeterminate();
            return boolR(false);
        }
        case Kind::Implies: {
            if (n.children.size() < 2) return boolR(true);
            // (=> a1 a2 ... an b) === ((a1∧...∧an) -> b)
            bool anyIndet = false;
            for (size_t i = 0; i + 1 < n.children.size(); ++i) {
                R p = eval(n.children[i]);
                if (p.kind == Kind3::Bool) {
                    if (!p.b) return boolR(true);  // false premise: implication true
                } else {
                    anyIndet = true;
                }
            }
            R q = eval(n.children.back());
            if (q.kind == Kind3::Bool && q.b) return boolR(true);
            if (anyIndet) return indeterminate();
            if (q.kind == Kind3::Bool) return boolR(false);
            return indeterminate();
        }
        case Kind::Xor: {
            bool acc = false;
            for (ExprId c : n.children) {
                R r = eval(c);
                if (r.kind != Kind3::Bool) return indeterminate();
                acc = acc != r.b;
            }
            return boolR(acc);
        }
        case Kind::Ite: {
            if (n.children.size() != 3) return indeterminate();
            R cond = eval(n.children[0]);
            if (cond.kind != Kind3::Bool) {
                // Branch-Indeterminate: if both branches agree on value, OK;
                // else Indeterminate (sound).
                R t = eval(n.children[1]);
                R f = eval(n.children[2]);
                if (t.kind == Kind3::Bool && f.kind == Kind3::Bool && t.b == f.b)
                    return boolR(t.b);
                return indeterminate();
            }
            return eval(cond.b ? n.children[1] : n.children[2]);
        }
        default:
            // Arithmetic / BV / FP / quantifiers / etc — Indeterminate (sound).
            return indeterminate();
    }
}

DtModelValidator::Verdict DtModelValidator::validate(
    const std::vector<ExprId>& assertions) {
    bool anyIndet = false;
    const bool diag = std::getenv("XOLVER_DT_VALIDATE_PER_ASSERT") != nullptr;
    size_t nIndet = 0, nTrue = 0, nFalse = 0;
    for (ExprId a : assertions) {
        R r = eval(a);
        if (r.kind == Kind3::Bool) {
            if (r.b) ++nTrue; else ++nFalse;
            if (!r.b) {
                if (diag) std::cerr << "[DT-VAL-ASSERT] expr=" << a << " VIOLATED\n";
                return Verdict::Violated;
            }
        } else {
            ++nIndet;
            if (diag) std::cerr << "[DT-VAL-ASSERT] expr=" << a << " kind=" << (int)r.kind << " indet\n";
            anyIndet = true;
        }
    }
    if (diag) std::cerr << "[DT-VAL] tally true=" << nTrue << " indet=" << nIndet << " false=" << nFalse << "\n";
    return anyIndet ? Verdict::Indeterminate : Verdict::Satisfied;
}

} // namespace xolver
