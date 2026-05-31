#include "theory/datatype/DtModelValidator.h"
#include <cstring>
#include <iostream>
#include <cstdlib>

namespace xolver {

namespace {
constexpr char kCtorPrefix[]   = "#dt.ctor.";
constexpr char kSelPrefix[]    = "#dt.sel.";
constexpr char kTesterPrefix[] = "#dt.is.";
}  // namespace

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

DtModelValidator::TreePtr DtModelValidator::extractTree(EClassId c) {
    auto cached = treeMemo_.find(c);
    if (cached != treeMemo_.end()) return cached->second;

    // Cycle guard: a recursive call hitting a class already being expanded
    // must terminate. Acyclicity DFS in DtReasoner makes this unreachable in
    // a well-formed sat state, but the guard is sound regardless.
    if (inProgress_.count(c)) {
        auto t = std::make_shared<Tree>();
        t->opaqueCls = c;
        return t;
    }

    auto t = std::make_shared<Tree>();
    std::string ctorName = constructorOfClass(c);
    if (ctorName.empty()) {
        t->opaqueCls = c;
        treeMemo_[c] = t;
        return t;
    }

    EufTermId ctorTerm = constructorTermInClass(c, ctorName);
    if (ctorTerm == NullEufTerm) {
        t->opaqueCls = c;
        treeMemo_[c] = t;
        return t;
    }

    inProgress_.insert(c);
    t->hasCtor = true;
    t->ctorName = ctorName;
    const auto& args = tm_.node(ctorTerm).args;
    t->children.reserve(args.size());
    for (EufTermId a : args) {
        EClassId ca = egraph_.rep(a);
        t->children.push_back(extractTree(ca));
    }
    inProgress_.erase(c);
    treeMemo_[c] = t;
    return t;
}

DtModelValidator::R DtModelValidator::compareTrees(const TreePtr& a, const TreePtr& b) {
    R r;
    if (!a || !b) { r.kind = Kind3::Indeterminate; return r; }
    if (a->hasCtor && b->hasCtor) {
        if (a->ctorName != b->ctorName) { r.kind = Kind3::Bool; r.b = false; return r; }
        if (a->children.size() != b->children.size()) {
            r.kind = Kind3::Bool; r.b = false; return r;
        }
        bool indet = false;
        for (size_t i = 0; i < a->children.size(); ++i) {
            R sub = compareTrees(a->children[i], b->children[i]);
            if (sub.kind == Kind3::Bool) {
                if (!sub.b) { r.kind = Kind3::Bool; r.b = false; return r; }
            } else {
                indet = true;
            }
        }
        if (indet) { r.kind = Kind3::Indeterminate; return r; }
        r.kind = Kind3::Bool; r.b = true; return r;
    }
    if (!a->hasCtor && !b->hasCtor) {
        if (a->opaqueCls == b->opaqueCls) { r.kind = Kind3::Bool; r.b = true; return r; }
        r.kind = Kind3::Indeterminate; return r;
    }
    r.kind = Kind3::Indeterminate; return r;
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
        case Kind::UFApply: {
            EufTermId t = tm_.findTerm(e);
            if (t == NullEufTerm) return indeterminate();
            // Boolean: read off true/false sentinel class merge.
            if (n.sort == ir_.boolSortId()) {
                EufTermId trueT = tm_.trueConstant();
                EufTermId falseT = tm_.falseConstant();
                if (trueT != NullEufTerm && egraph_.same(t, trueT)) return boolR(true);
                if (falseT != NullEufTerm && egraph_.same(t, falseT)) return boolR(false);
                return indeterminate();
            }
            EClassId c = egraph_.rep(t);
            if (dts_.isDatatypeSort(n.sort)) {
                R r; r.kind = Kind3::DtTree; r.tree = extractTree(c); r.cls = c;
                return store(r);
            }
            // Numeric or other opaque: e-class identity only.
            R r; r.kind = Kind3::Opaque; r.cls = c; return store(r);
        }
        case Kind::Constructor: {
            // Build tree directly from arg ExprIds — does NOT consult the
            // e-graph for the result class identity, but each ARG is evaluated
            // recursively (DT args contribute structural subtrees, opaque args
            // contribute Opaque leaves with their class).
            R r; r.kind = Kind3::DtTree;
            auto t = std::make_shared<Tree>();
            t->hasCtor = true;
            const std::string* name = std::get_if<std::string>(&n.payload.value);
            t->ctorName = name ? *name : std::string();
            t->children.reserve(n.children.size());
            for (ExprId c : n.children) {
                R child = eval(c);
                if (child.kind == Kind3::DtTree && child.tree) {
                    t->children.push_back(child.tree);
                } else {
                    auto leaf = std::make_shared<Tree>();
                    leaf->opaqueCls = child.cls;
                    t->children.push_back(leaf);
                }
            }
            r.tree = t;
            EufTermId tm = tm_.findTerm(e);
            if (tm != NullEufTerm) r.cls = egraph_.rep(tm);
            return store(r);
        }
        case Kind::Selector: {
            if (n.children.size() != 1) return indeterminate();
            R x = eval(n.children[0]);
            const std::string* name = std::get_if<std::string>(&n.payload.value);
            std::string selName = name ? *name : std::string();
            SortId opSort = ir_.get(n.children[0]).sort;

            // If operand evaluates to an opaque (no constructor witness),
            // fall back to the selector term's own e-class identity. Sound:
            // the operand is unconstrained, so the selector value is too.
            if (x.kind != Kind3::DtTree || !x.tree) {
                EufTermId selT = tm_.findTerm(e);
                if (selT == NullEufTerm) return indeterminate();
                EClassId c = egraph_.rep(selT);
                if (dts_.isDatatypeSort(n.sort)) {
                    R r; r.kind = Kind3::DtTree; r.tree = extractTree(c); r.cls = c;
                    return store(r);
                }
                R r; r.kind = Kind3::Opaque; r.cls = c; return store(r);
            }

            // Operand is a tree. Two cases:
            //  - tree has a constructor: if that ctor OWNS this selector,
            //    return the structural value of the matching child. If the
            //    ctor is a SIBLING (doesn't own this selector), the SMT-LIB
            //    semantics are underspecified → Indeterminate (NOT a clash).
            //  - tree is opaque-with-ctor-less: fall through to e-class above.
            if (x.tree->hasCtor) {
                uint32_t argIdx = 0;
                const DtConstructorInfo* owner = dts_.selector(opSort, selName, argIdx);
                if (!owner) return indeterminate();
                if (owner->name != x.tree->ctorName) {
                    return indeterminate();  // SMT-LIB underspecified
                }
                if (argIdx >= x.tree->children.size()) return indeterminate();
                TreePtr child = x.tree->children[argIdx];
                if (dts_.isDatatypeSort(n.sort)) {
                    R r; r.kind = Kind3::DtTree; r.tree = child; return store(r);
                }
                // Selector returns a non-DT sort (Int/Bool/uninterp). The tree
                // child is structural over DT; for non-DT children we kept the
                // opaque class id from the original child eval. Emit Opaque.
                R r; r.kind = Kind3::Opaque;
                if (child) r.cls = child->opaqueCls;
                return store(r);
            }

            // No structural ctor info: fall back to e-class identity.
            EufTermId selT = tm_.findTerm(e);
            if (selT == NullEufTerm) return indeterminate();
            EClassId c = egraph_.rep(selT);
            if (dts_.isDatatypeSort(n.sort)) {
                R r; r.kind = Kind3::DtTree; r.tree = extractTree(c); r.cls = c;
                return store(r);
            }
            R r; r.kind = Kind3::Opaque; r.cls = c; return store(r);
        }
        case Kind::Tester: {
            if (n.children.size() != 1) return indeterminate();
            R x = eval(n.children[0]);
            const std::string* targetNm = std::get_if<std::string>(&n.payload.value);
            std::string target = targetNm ? *targetNm : std::string();
            if (target.rfind("is-", 0) == 0) target = target.substr(3);
            if (target.empty()) return indeterminate();
            if (x.kind == Kind3::DtTree && x.tree && x.tree->hasCtor) {
                return boolR(x.tree->ctorName == target);
            }
            return indeterminate();
        }
        case Kind::Eq: {
            if (n.children.size() < 2) return boolR(true);
            R a = eval(n.children[0]);
            bool indet = false;
            for (size_t i = 1; i < n.children.size(); ++i) {
                R b = eval(n.children[i]);
                if (a.kind == Kind3::Bool && b.kind == Kind3::Bool) {
                    if (a.b != b.b) return boolR(false);
                } else if (a.kind == Kind3::DtTree && b.kind == Kind3::DtTree) {
                    R cmp = compareTrees(a.tree, b.tree);
                    if (cmp.kind == Kind3::Bool) {
                        if (!cmp.b) return boolR(false);
                    } else {
                        // Structural Indeterminate — but if the surface terms
                        // happen to share an e-class, that's a sound positive
                        // (the e-graph asserts them equal).
                        if (a.cls != static_cast<EClassId>(-1) &&
                            a.cls == b.cls) {
                            // proven equal by e-graph
                        } else {
                            indet = true;
                        }
                    }
                } else if (a.kind == Kind3::Opaque && b.kind == Kind3::Opaque) {
                    if (a.cls == b.cls) {
                        // equal by e-graph
                    } else {
                        indet = true;
                    }
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
            std::vector<R> vs;
            vs.reserve(n.children.size());
            for (ExprId c : n.children) vs.push_back(eval(c));
            bool indet = false;
            for (size_t i = 0; i < vs.size(); ++i) {
                for (size_t j = i + 1; j < vs.size(); ++j) {
                    if (vs[i].kind == Kind3::Bool && vs[j].kind == Kind3::Bool) {
                        if (vs[i].b == vs[j].b) return boolR(false);
                    } else if (vs[i].kind == Kind3::DtTree && vs[j].kind == Kind3::DtTree) {
                        R cmp = compareTrees(vs[i].tree, vs[j].tree);
                        if (cmp.kind == Kind3::Bool) {
                            if (cmp.b) return boolR(false);
                        } else if (vs[i].cls != static_cast<EClassId>(-1) &&
                                   vs[i].cls == vs[j].cls) {
                            return boolR(false);
                        } else { indet = true; }
                    } else if (vs[i].kind == Kind3::Opaque && vs[j].kind == Kind3::Opaque) {
                        if (vs[i].cls == vs[j].cls) return boolR(false);
                        indet = true;
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
            bool anyIndet = false;
            for (size_t i = 0; i + 1 < n.children.size(); ++i) {
                R p = eval(n.children[i]);
                if (p.kind == Kind3::Bool) {
                    if (!p.b) return boolR(true);
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
                R t = eval(n.children[1]);
                R f = eval(n.children[2]);
                if (t.kind == Kind3::Bool && f.kind == Kind3::Bool && t.b == f.b)
                    return boolR(t.b);
                return indeterminate();
            }
            return eval(cond.b ? n.children[1] : n.children[2]);
        }
        default:
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
    if (anyIndet) {
        // Strict mode (XOLVER_DT_VALIDATOR_STRICT): promote Indeterminate to
        // Violated. Sound: if validate() can't ground an assertion fully under
        // the live e-graph at a Full-effort sat check, we cannot CERTIFY sat,
        // so flooring to Violated → Unknown is correct. The trade-off is over-
        // flooring true-sat cases whose model uses opaque DT classes. Master's
        // 5min batch surfaced 43 false-SATs that lenient mode missed (e-graph
        // state arrived at a sat verdict without enough constructor witnesses
        // for structural eval) — use strict when the false-SAT cost dominates.
        if (strict_) {
            if (diag) std::cerr << "[DT-VAL] strict: Indet -> Violated (" << nIndet << " indet asserts)\n";
            return Verdict::Violated;
        }
        return Verdict::Indeterminate;
    }
    return Verdict::Satisfied;
}

} // namespace xolver
