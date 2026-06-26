// Xolver Python bindings (_xolver) — a thin pybind11 layer over the public C++
// API in include/xolver/. The Pythonic, z3-like surface (Int/Real/Bool,
// operator overloading, solve()) lives in the pure-Python package on top of
// this; here we expose the C++ types as faithfully and minimally as possible.
//
// The one internal dependency is the expr Kind enum (the opcode set that
// Solver::mkOp takes as a uint32_t) — it is effectively part of the public
// contract already, since mkOp's argument IS a Kind value.

#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/operators.h>

#include <xolver/xolver.h>
#include "expr/ir.h"  // xolver::Kind — the mkOp opcode enum

#include <iostream>
#include <sstream>
#include <string>

namespace py = pybind11;
using namespace xolver;

namespace {

// The solver writes search diagnostics to std::cerr; the CLI swallows stderr on
// its worker thread (the SMT-COMP contract reads only stdout). Mirror that for
// the binding: mute std::cerr for the duration of a solve unless the user opted
// into verbose mode. Scoped (RAII), restoring the original buffer on exit.
bool g_verbose = false;

struct CerrMute {
    std::streambuf* old_ = nullptr;
    std::ostringstream sink_;
    explicit CerrMute(bool mute) {
        if (mute) old_ = std::cerr.rdbuf(sink_.rdbuf());
    }
    ~CerrMute() {
        if (old_) std::cerr.rdbuf(old_);
    }
};

// Render an ostream-dumping method to a Python str.
template <typename Fn>
std::string dumpToString(Fn&& fn) {
    std::ostringstream os;
    fn(os);
    return os.str();
}

// Trampoline: lets a Python subclass of xolver.Propagator override the hooks.
// The callbacks fire while checkSat() holds the GIL, so the override lookups are
// safe (pybind reacquires the already-held GIL). Registering a propagator is
// opt-in; the per-callback Python dispatch cost is only paid when one is set.
using LemmaList = std::vector<std::vector<int>>;  // dodge the macro-comma below

class PyPropagator : public Propagator {
public:
    using Propagator::Propagator;
    // --- setup / SAT level ---
    void onSetup(const std::vector<ObservedAtom>& atoms) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_setup", onSetup, atoms);
    }
    void onAssignment(uint32_t var, bool value, bool isDecision) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_assignment", onAssignment,
                               var, value, isDecision);
    }
    void onNewDecisionLevel() override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_new_decision_level",
                               onNewDecisionLevel);
    }
    void onBacktrack(uint32_t level) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_backtrack", onBacktrack, level);
    }
    int decide() override {
        PYBIND11_OVERRIDE_NAME(int, Propagator, "decide", decide);
    }
    // --- SMT / theory level ---
    void onFixed(uint32_t var, bool value, Term atom) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_fixed", onFixed,
                               var, value, atom);
    }
    void onTheoryCheck(CheckEffort effort, CheckOutcome outcome) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_theory_check", onTheoryCheck,
                               effort, outcome);
    }
    void onConflict(const std::vector<int>& clause) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_conflict", onConflict, clause);
    }
    void onLemma(const std::vector<int>& clause) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_lemma", onLemma, clause);
    }
    void onPropagate(const std::vector<int>& clause) override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_propagate", onPropagate, clause);
    }
    void onFinalCheck() override {
        PYBIND11_OVERRIDE_NAME(void, Propagator, "on_final_check", onFinalCheck);
    }
    // --- generation ---
    LemmaList generateLemmas() override {
        PYBIND11_OVERRIDE_NAME(LemmaList, Propagator, "generate_lemmas",
                               generateLemmas);
    }
};

}  // namespace

PYBIND11_MODULE(_xolver, m) {
    m.doc() = "Xolver SMT solver — low-level C++ bindings (use the `xolver` "
              "package for the Pythonic API).";

    // Verbose mode: when true, the solver's std::cerr diagnostics are shown;
    // when false (default), they are muted during solves (the CLI does the same).
    m.def("set_verbose", [](bool v) { g_verbose = v; }, py::arg("verbose"),
          "Show (true) or mute (false, default) solver stderr diagnostics.");
    m.def("get_verbose", []() { return g_verbose; });

    // ----- Result --------------------------------------------------------
    py::enum_<Result>(m, "Result", "Verdict of a check-sat query.")
        .value("Sat", Result::Sat)
        .value("Unsat", Result::Unsat)
        .value("Unknown", Result::Unknown);
    m.def("result_to_string", &xolver::toString, py::arg("result"));

    // ----- Kind (mkOp opcode set) ---------------------------------------
    // Curated subset of expr/ir.h Kind needed to build formulas; values come
    // straight from the enum so they stay in sync with the core.
    py::enum_<Kind>(m, "Kind", "Operator kinds for Solver.mk_op.")
        .value("Not", Kind::Not).value("And", Kind::And).value("Or", Kind::Or)
        .value("Implies", Kind::Implies).value("Xor", Kind::Xor).value("Ite", Kind::Ite)
        .value("Add", Kind::Add).value("Sub", Kind::Sub).value("Neg", Kind::Neg)
        .value("Mul", Kind::Mul).value("Div", Kind::Div).value("Mod", Kind::Mod)
        .value("Abs", Kind::Abs).value("Pow", Kind::Pow)
        .value("Eq", Kind::Eq).value("Distinct", Kind::Distinct)
        .value("Lt", Kind::Lt).value("Leq", Kind::Leq)
        .value("Gt", Kind::Gt).value("Geq", Kind::Geq)
        .value("ToInt", Kind::ToInt).value("ToReal", Kind::ToReal).value("IsInt", Kind::IsInt)
        .value("Select", Kind::Select).value("Store", Kind::Store).value("ConstArray", Kind::ConstArray);

    // ----- Sort ----------------------------------------------------------
    py::class_<Sort>(m, "Sort", "Opaque handle for a solver sort.")
        .def(py::init<>())
        .def("id", &Sort::id)
        .def("is_null", &Sort::isNull)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__hash__", [](const Sort& s) { return s.id(); })
        .def("__repr__", [](const Sort& s) {
            return "<xolver.Sort id=" + std::to_string(s.id()) + ">";
        });

    // ----- Term ----------------------------------------------------------
    py::class_<Term>(m, "Term", "Opaque handle for a solver term.")
        .def(py::init<>())
        .def("id", &Term::id)
        .def("is_null", &Term::isNull)
        .def(py::self == py::self)
        .def(py::self != py::self)
        .def("__hash__", [](const Term& t) { return t.id(); })
        .def("__repr__", [](const Term& t) {
            return "<xolver.Term id=" + std::to_string(t.id()) + ">";
        });

    // ----- Model ---------------------------------------------------------
    py::class_<Model>(m, "Model", "Variable assignments from a sat query.")
        .def("is_empty", &Model::isEmpty)
        .def("get_value",
             [](const Model& mdl, uint32_t varId) -> py::object {
                 const std::string* v = mdl.getValue(varId);
                 if (!v) return py::none();
                 return py::cast(*v);
             },
             py::arg("var_id"))
        .def("values", &Model::values);

    // ----- One-step control: ObservedAtom + Propagator -------------------
    py::class_<ObservedAtom>(m, "ObservedAtom",
                             "An observable atom: SAT var + the term it encodes.")
        .def_readonly("var", &ObservedAtom::var)
        .def_readonly("term", &ObservedAtom::term)
        .def_readonly("is_theory", &ObservedAtom::isTheory)
        .def("__repr__", [](const ObservedAtom& a) {
            return "<ObservedAtom var=" + std::to_string(a.var) +
                   " term=" + std::to_string(a.term.id()) +
                   (a.isTheory ? " theory>" : " bool>");
        });

    py::enum_<CheckEffort>(m, "CheckEffort", "Effort of a theory consistency check.")
        .value("Standard", CheckEffort::Standard)
        .value("Full", CheckEffort::Full);
    py::enum_<CheckOutcome>(m, "CheckOutcome", "Outcome of a theory consistency check.")
        .value("Consistent", CheckOutcome::Consistent)
        .value("Conflict", CheckOutcome::Conflict)
        .value("Lemma", CheckOutcome::Lemma)
        .value("Unknown", CheckOutcome::Unknown);

    py::class_<Propagator, PyPropagator>(m, "Propagator",
        "User propagator base class — subclass and override hooks to observe and "
        "steer the CDCL(T) search at both the SAT and the SMT/theory level.")
        .def(py::init<>())
        // setup / SAT level
        .def("on_setup", &Propagator::onSetup, py::arg("atoms"))
        .def("on_assignment", &Propagator::onAssignment,
             py::arg("var"), py::arg("value"), py::arg("is_decision"))
        .def("on_new_decision_level", &Propagator::onNewDecisionLevel)
        .def("on_backtrack", &Propagator::onBacktrack, py::arg("level"))
        .def("decide", &Propagator::decide)
        // SMT / theory level
        .def("on_fixed", &Propagator::onFixed,
             py::arg("var"), py::arg("value"), py::arg("atom"))
        .def("on_theory_check", &Propagator::onTheoryCheck,
             py::arg("effort"), py::arg("outcome"))
        .def("on_conflict", &Propagator::onConflict, py::arg("clause"))
        .def("on_lemma", &Propagator::onLemma, py::arg("clause"))
        .def("on_propagate", &Propagator::onPropagate, py::arg("clause"))
        .def("on_final_check", &Propagator::onFinalCheck)
        // generation (advanced)
        .def("generate_lemmas", &Propagator::generateLemmas);

    // ----- Solver --------------------------------------------------------
    py::class_<Solver>(m, "Solver", "Low-level Xolver solver handle.")
        .def(py::init<>())

        // Context
        .def("reset", &Solver::reset)
        .def("push", &Solver::push)
        .def("pop", &Solver::pop, py::arg("n") = 1u)

        // Options
        .def("set_logic",
             [](Solver& s, const std::string& logic) { s.setLogic(logic); },
             py::arg("logic"))
        .def("set_option",
             [](Solver& s, const std::string& key, const py::object& v) {
                 // bool BEFORE int — Python bool is a subclass of int.
                 if (py::isinstance<py::bool_>(v))
                     s.setOption(key, OptionValue(py::cast<bool>(v)));
                 else if (py::isinstance<py::int_>(v))
                     s.setOption(key, OptionValue(static_cast<int64_t>(py::cast<int64_t>(v))));
                 else if (py::isinstance<py::float_>(v))
                     s.setOption(key, OptionValue(py::cast<double>(v)));
                 else
                     s.setOption(key, OptionValue(std::string_view(py::cast<std::string>(v))));
             },
             py::arg("key"), py::arg("value"))
        .def("get_option",
             [](const Solver& s, const std::string& key) -> py::object {
                 OptionValue ov = s.getOption(key);
                 switch (ov.kind) {
                     case OptionValue::Bool:   return py::cast(ov.b);
                     case OptionValue::Int:    return py::cast(ov.i);
                     case OptionValue::Double: return py::cast(ov.d);
                     case OptionValue::String: return py::cast(ov.s);
                 }
                 return py::none();
             },
             py::arg("key"))

        // Sorts
        .def("bool_sort", &Solver::boolSort)
        .def("int_sort", &Solver::intSort)
        .def("real_sort", &Solver::realSort)
        .def("bv_sort", &Solver::bvSort, py::arg("width"))
        .def("fp_sort", &Solver::fpSort, py::arg("ebits"), py::arg("sbits"))

        // Terms
        .def("mk_const",
             [](Solver& s, Sort srt, const std::string& name) { return s.mkConst(srt, name); },
             py::arg("sort"), py::arg("name"))
        .def("mk_var",
             [](Solver& s, Sort srt, const std::string& name) { return s.mkVar(srt, name); },
             py::arg("sort"), py::arg("name"))
        .def("mk_bool", &Solver::mkBool, py::arg("value"))
        .def("mk_int", &Solver::mkInt, py::arg("value"))
        .def("mk_real", &Solver::mkReal, py::arg("rational"))
        .def("mk_op",
             [](Solver& s, Kind k, std::vector<Term> args) {
                 return s.mkOp(static_cast<uint32_t>(k), std::move(args));
             },
             py::arg("kind"), py::arg("args"))

        // Parsing
        .def("parse_file",
             [](Solver& s, const std::string& path) { return s.parseFile(path); },
             py::arg("filename"))

        // Assertions / solving
        .def("assert_formula", &Solver::assertFormula, py::arg("f"))
        .def("check_sat",
             [](Solver& s) { CerrMute mute(!g_verbose); return s.checkSat(); })
        .def("check_sat_assuming",
             [](Solver& s, std::vector<Term> a) {
                 CerrMute mute(!g_verbose);
                 return s.checkSatAssuming(std::move(a));
             },
             py::arg("assumptions"))

        // One-step control (keep the propagator alive as long as the solver).
        .def("set_propagator", &Solver::setPropagator, py::arg("propagator"),
             py::keep_alive<1, 2>())
        .def("clear_propagator", &Solver::clearPropagator)

        // Results
        .def("get_model", &Solver::getModel)
        .def("get_value", &Solver::getValue, py::arg("t"))
        .def("get_unsat_core", &Solver::getUnsatCore)
        .def("unsat_core_requested", &Solver::unsatCoreRequested)
        .def("dump_unsat_core",
             [](const Solver& s) { return dumpToString([&](std::ostream& os) { s.dumpUnsatCore(os); }); })
        .def("model_requested", &Solver::modelRequested)
        .def("dump_model",
             [](const Solver& s) { return dumpToString([&](std::ostream& os) { s.dumpModel(os); }); })
        .def("model_matches_original", &Solver::modelMatchesOriginal)

        // Unknown diagnosis
        .def("last_unknown_reason", &Solver::lastUnknownReason)
        .def("last_unknown_code", &Solver::lastUnknownCode)
        .def("last_unknown_component", &Solver::lastUnknownComponent)
        .def("last_unknown_detail", &Solver::lastUnknownDetail)

        // Debug / research
        .def("dump_smt2",
             [](Solver& s) { return dumpToString([&](std::ostream& os) { s.dumpSMT2(os); }); })
        .def("dump_features",
             [](const Solver& s) { return dumpToString([&](std::ostream& os) { s.dumpFeatures(os); }); });

    // Version (compiled-in).
    m.attr("__version__") = py::str(
        std::to_string(XOLVER_VERSION_MAJOR) + "." +
        std::to_string(XOLVER_VERSION_MINOR) + "." +
        std::to_string(XOLVER_VERSION_PATCH));
}
