#include <doctest/doctest.h>
#include "xolver/Script.h"
#include <stdexcept>

TEST_CASE("script snapshots isolate query contexts and assumptions") {
    auto q = xolver::smtQuerySnapshots(
        "(declare-const p Bool)(assert p)"
        "(check-sat-assuming ((not p)))"
        "(check-sat)(push 1)(assert false)(check-sat)(pop 1)");
    REQUIRE(q.size() == 3);
    CHECK(q[0].find("(not p)") != std::string::npos);
    CHECK(q[1].find("(not p)") == std::string::npos);
    CHECK(q[1].find("(assert false)") == std::string::npos);
    CHECK(q[2].find("(assert false)") != std::string::npos);
    CHECK(q[2].find("(pop 1)") == std::string::npos);
}

TEST_CASE("script snapshots respect strings quoted symbols comments and exit") {
    auto q = xolver::smtQuerySnapshots(
        "; (check-sat)\n(declare-const |p);x| Bool)"
        "(echo \"a;()\"\"b\")(check-sat-assuming (|p);x| ; )\n) ; trailing\n)"
        "(get-value (|p);x|))(exit) garbage after exit");
    REQUIRE(q.size() == 1);
    CHECK(q[0].find("(assert (and |p);x|") != std::string::npos);
    CHECK(q[0].find("(get-value (|p);x|))") != std::string::npos);
    CHECK(q[0].find("garbage") == std::string::npos);
    CHECK_THROWS_AS(xolver::smtQuerySnapshots("(check-sat"), std::invalid_argument);
    CHECK_THROWS_AS(xolver::smtQuerySnapshots("(check-sat-assuming (p) (q))"), std::invalid_argument);
    CHECK_THROWS_AS(xolver::smtQuerySnapshots("(check-sat)(assert false)(get-model)"), std::invalid_argument);
}
