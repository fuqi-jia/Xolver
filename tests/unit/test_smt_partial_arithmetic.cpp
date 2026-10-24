#include <doctest/doctest.h>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <xolver/Solver.h>

using namespace xolver;
TEST_CASE("SMT arithmetic: div and mod select a query-local combination") {
    struct Example {
        const char *logic;
        const char *body;
        Result expected;
    };
    const Example examples[] = {
        {"QF_NIA",
         "(declare-const x Int)(declare-const d Int)"
         "(assert (>= x 0))(assert (> d 0))(assert (> (div x d) x))",
         Result::Unsat},
        {"QF_NIA",
         "(declare-const x Int)(declare-const d Int)"
         "(assert (>= x 0))(assert (> d 0))(assert (> (mod x d) x))",
         Result::Unsat},
        {"QF_NIA", "(declare-const x Int)(assert (= (div x 0) 5))", Result::Sat},
        {"QF_LIA", "(declare-const x Int)(assert (= (mod x 0) 7))", Result::Sat},
        {"ALL", "(declare-const x Int)(assert (= (div x 0) 5))", Result::Sat},
    };
    auto path = std::filesystem::temp_directory_path() / "xolver_partial_arithmetic.smt2";
    for (const auto &example : examples) {
        INFO(std::string(example.logic), ": ", std::string(example.body));
        {
            std::ofstream out(path);
            out << "(set-logic " << example.logic << ")" << example.body << "(check-sat)";
        }
        Solver solver;
        REQUIRE(solver.parseFile(path.string()));
        for (int iteration = 0; iteration < 2; ++iteration) {
            auto result = solver.checkSat();
            INFO(solver.lastUnknownReason());
            REQUIRE((result == example.expected));
            if (result == Result::Sat)
                CHECK((solver.validateModel() == Solver::ModelValidation::Satisfied));
            std::ostringstream features;
            solver.dumpFeatures(features);
            CHECK(features.str().find(std::string("\"logic\":\"") + example.logic + "\"") !=
                  std::string::npos);
        }
        solver.push();
        solver.assertFormula(solver.mkBool(false));
        CHECK((solver.checkSat() == Result::Unsat));
        solver.pop();
        CHECK((solver.checkSat() == example.expected));
    }
    std::filesystem::remove(path);
}
