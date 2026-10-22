#include <doctest/doctest.h>
#include "base/EnvParam.h"
#include "base/RuntimeConfig.h"
#include "base/SolveClock.h"
#include "xolver/Solver.h"
#include <atomic>
#include <barrier>
#include <thread>
#include <stdexcept>
#include <type_traits>

using namespace xolver;

TEST_CASE("typed controls preserve distinct historical Boolean readers") {
    using namespace config;
    static_assert(std::is_same_v<decltype(read<ReadKind::Flag>("XOLVER_TEST_TYPED")), bool>);
    static_assert(std::is_same_v<decltype(read<ReadKind::Int>("XOLVER_TEST_TYPED", 0)), int>);
    for (const std::string value : {"", "0", "00", "01", "1", "abc"}) {
        CAPTURE(value);
        env::Scope scope(env::Snapshot::capture({{"XOLVER_TEST_TYPED", value}}));
        CHECK(read<ReadKind::Presence>("XOLVER_TEST_TYPED"));
        CHECK(read<ReadKind::Flag>("XOLVER_TEST_TYPED") == (!value.empty() && value.front() != '0'));
    }
    {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_TEST_TYPED", "37"}}));
        CHECK(read<ReadKind::Int>("XOLVER_TEST_TYPED", 9) == 37);
        env::Scope nested(env::Snapshot::capture({{"XOLVER_TEST_TYPED", "9999999999999999999999"}}));
        CHECK(read<ReadKind::Int>("XOLVER_TEST_TYPED", 9) == 9);
    }
}

TEST_CASE("runtime configuration: nested defaults and exceptions restore snapshots") {
    env::Scope outer(env::Snapshot::capture({{"XOLVER_TEST_NESTED_DEFAULT", "0"},
                                            {"XOLVER_TEST_NESTED_BUDGET", "17"}}));
    const auto baseline = env::currentSnapshot();
    try {
        env::Scope arm(baseline.withDefaults({{"XOLVER_TEST_NESTED_DEFAULT", "1"},
                                             {"XOLVER_TEST_ARM_ONLY", "1"}}));
        CHECK_FALSE(env::flag("XOLVER_TEST_NESTED_DEFAULT"));
        CHECK(env::flag("XOLVER_TEST_ARM_ONLY"));
        CHECK(env::paramInt("XOLVER_TEST_NESTED_BUDGET", 0) == 17);
        throw std::runtime_error("unwind");
    } catch (const std::runtime_error&) {}
    CHECK_FALSE(env::flag("XOLVER_TEST_ARM_ONLY"));
    CHECK_FALSE(env::flag("XOLVER_TEST_NESTED_DEFAULT"));
}

TEST_CASE("runtime configuration: snapshots isolate simultaneous threads") {
    std::barrier sync(2);
    std::atomic<int> errors{0};
    auto run = [&](int value) {
        env::Scope scope(env::Snapshot::capture({
            {"XOLVER_TEST_THREAD_VALUE", std::to_string(value)}}));
        sync.arrive_and_wait();
        for (int i = 0; i < 1000; ++i)
            if (env::paramInt("XOLVER_TEST_THREAD_VALUE", -1) != value) ++errors;
    };
    std::jthread a(run, 23), b(run, 42);
    a.join(); b.join();
    CHECK(errors == 0);
}

TEST_CASE("runtime configuration: wall scaling no longer keeps the first query value") {
    wall::beginSolve(100000);
    {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_WALLCLOCK_SCALE", "0"}}));
        CHECK(wall::scaledCount(2, 1, 8) == 2);
    }
    {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_WALLCLOCK_SCALE", "1"}}));
        CHECK(wall::scaledCount(2, 1, 8) == 16);
    }
    wall::endSolve();
}

TEST_CASE("runtime configuration: solver parameters reject embedded nul") {
    Solver s;
    CHECK_THROWS_AS(s.setRuntimeParameter("", "1"), std::invalid_argument);
    CHECK_THROWS_AS(s.setRuntimeParameter("A=B", "1"), std::invalid_argument);
    CHECK_THROWS_AS(s.setRuntimeParameter(std::string("A\0B", 3), "1"), std::invalid_argument);
    CHECK_THROWS_AS(s.setRuntimeParameter("A", std::string("1\0", 2)), std::invalid_argument);
    s.setRuntimeParameter("XOLVER_TEST_PARAMETER", "1");
    s.assertFormula(s.mkBool(false));
    CHECK((s.checkSat() == Result::Unsat));
    s.clearRuntimeParameter("XOLVER_TEST_PARAMETER");
    CHECK((s.checkSat() == Result::Unsat));
}

TEST_CASE("typed controls: semantic Booleans agree across all token spellings") {
    using namespace config;
    for (const char* token : {"1", "true", "TRUE", "yes", "On"}) {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_TEST_BOOLEAN", token}}));
        CHECK(read<ReadKind::Boolean>("XOLVER_TEST_BOOLEAN"));
    }
    for (const char* token : {"0", "false", "FALSE", "no", "Off"}) {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_TEST_BOOLEAN", token}}));
        CHECK_FALSE(read<ReadKind::Boolean>("XOLVER_TEST_BOOLEAN", true));
    }
    for (const char* token : {"", "00", "garbage"}) {
        env::Scope scope(env::Snapshot::capture({{"XOLVER_TEST_BOOLEAN", token}}));
        CHECK_FALSE(read<ReadKind::Boolean>("XOLVER_TEST_BOOLEAN"));
        CHECK(read<ReadKind::Boolean>("XOLVER_TEST_BOOLEAN", true));
    }
}

TEST_CASE("typed controls: paths are owned and profile switches have defined defaults") {
    using namespace config;
    std::filesystem::path saved;
    {
        env::Scope scope(env::Snapshot::capture({
            {"XOLVER_NIA_FARKAS_DUMP_FILE", "/tmp/a directory/dump"},
            {"ARITH_STAGE_PROF", "true"}}));
        saved = read<ReadKind::Path>("XOLVER_NIA_FARKAS_DUMP_FILE");
        CHECK(read<ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/profile") == "/tmp/profile");
    }
    CHECK(saved == "/tmp/a directory/dump");
    {
        env::Scope scope(env::Snapshot::capture({
            {"ARITH_STAGE_PROF", "off"}, {"XOLVER_NIA_FARKAS_DUMP_FILE", ""}}));
        CHECK(read<ReadKind::ProfilePath>("ARITH_STAGE_PROF", "/tmp/profile").empty());
        CHECK(read<ReadKind::Path>("XOLVER_NIA_FARKAS_DUMP_FILE", "/tmp/default") == "/tmp/default");
    }
}

TEST_CASE("typed controls: budget and strategy parsing rejects partial and overflowing input") {
    using namespace config;
    {
        env::Scope scope(env::Snapshot::capture({
            {"XOLVER_NIA_MODULAR_MODULI", "2, 3,3, 97"},
            {"XOLVER_NRA_PROJECTION", "LaZaRd"},
            {"XOLVER_DECIDE_PROBE", "17"},
            {"XOLVER_SAT_LEMMA_MGMT", "1"}}));
        CHECK(read<ReadKind::Moduli>("XOLVER_NIA_MODULAR_MODULI") == std::vector<int>{2, 3, 97});
        CHECK((read<ReadKind::Projection>("XOLVER_NRA_PROJECTION") == Projection::Lazard));
        CHECK(read<ReadKind::Period>("XOLVER_DECIDE_PROBE") == 17);
        CHECK(read<ReadKind::Capacity>("XOLVER_SAT_LEMMA_MGMT") == 1);
    }
    for (const char* invalid : {"2,3,", "2,junk", "2,101", "9999999999999999999999999"}) {
        env::Scope scope(env::Snapshot::capture({
            {"XOLVER_NIA_MODULAR_MODULI", invalid},
            {"XOLVER_DECIDE_PROBE", invalid},
            {"XOLVER_SAT_LEMMA_MGMT", invalid}}));
        CHECK(read<ReadKind::Moduli>("XOLVER_NIA_MODULAR_MODULI") == std::vector<int>{2, 3, 4, 5, 7, 8, 9, 11});
        CHECK(read<ReadKind::Period>("XOLVER_DECIDE_PROBE") == 0);
        CHECK(read<ReadKind::Capacity>("XOLVER_SAT_LEMMA_MGMT") == 0);
    }
}
