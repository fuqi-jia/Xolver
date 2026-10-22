#include <doctest/doctest.h>
#include "xolver/Solver.h"
#include <filesystem>
#include <fstream>
#include <unistd.h>

TEST_CASE("native SL does not drop unused contradictory ordinary recursive equations") {
    const auto file = std::filesystem::temp_directory_path() /
        ("xolver-sl-recursive-boundary-" + std::to_string(getpid()) + ".smt2");
    {
        std::ofstream stream(file);
        stream << "(set-logic ALL)(declare-heap (Int Int))"
                  "(define-fun-rec p () Bool (not p))(assert true)(check-sat)";
    }
    xolver::Solver solver;
    const bool parsed = solver.parseFile(file.string());
    std::filesystem::remove(file);
    REQUIRE(parsed);
    CHECK((solver.checkSat() == xolver::Result::Unknown));
}
