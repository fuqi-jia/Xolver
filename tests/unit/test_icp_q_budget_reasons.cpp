#include <doctest/doctest.h>
#include "search/icp/IcpEngineQ.h"
#include <algorithm>

using namespace xolver;

namespace {
struct CountingContractorQ : ContractorQ {
    int& calls;
    explicit CountingContractorQ(int& count) : calls(count) {}
    ContractorResultQ contract(ReasonedBoxQ&) override {
        ++calls;
        return {IcpStatus::NoChange, std::nullopt, {}};
    }
    std::vector<std::string> vars() const override { return {}; }
    SatLit reason() const override { return SatLit::positive(1); }
};

// A contractor may expose a narrowed box through DomainUpdate. The engine
// must retain its proof even when no further contractor work is permitted.
struct EmptyingContractorQ : ContractorQ {
    int& calls;
    explicit EmptyingContractorQ(int& count) : calls(count) {}
    ContractorResultQ contract(ReasonedBoxQ& box) override {
        ++calls;
        box.narrow("x", IntervalQ{0, 1}, {reason()});
        const auto interval = box.get("x");
        return {IcpStatus::DomainUpdate, std::nullopt,
                {{"x", interval->interval, interval->reasons}}};
    }
    std::vector<std::string> vars() const override { return {"x"}; }
    SatLit reason() const override { return SatLit::negative(2); }
};
}

TEST_CASE("ICP-Q budget: zero and exact contractor limits are enforced before work") {
    for (int iterations : {0, 1, 2, 3})
    for (int limit : {0, 1, 2, 3}) {
        int calls = 0;
        std::vector<std::unique_ptr<ContractorQ>> contractors;
        for (int i = 0; i < 3; ++i)
            contractors.push_back(std::make_unique<CountingContractorQ>(calls));
        ReasonedBoxQ box;
        WatcherMap watchers;
        IcpConfig config;
        config.maxIterations = iterations;
        config.maxContractors = limit;
        const auto result = IcpEngineQ{}.run(contractors, watchers, box, config);
        CAPTURE(limit);
        CAPTURE(iterations);
        const auto allowed = std::min({iterations, limit, 3});
        CHECK(calls == allowed);
        CHECK(result.status == (allowed < 3 ? IcpStatus::UnknownBudget : IcpStatus::NoChange));
    }
}

TEST_CASE("ICP-Q reasons: an initially empty interval preserves both premises") {
    for (int work : {0, 1}) {
        const auto lower = SatLit::positive(1), upper = SatLit::negative(2);
        ReasonedBoxQ box;
        box.set("x", {IntervalQ{2, 1}, {lower, upper}});
        int calls = 0;
        std::vector<std::unique_ptr<ContractorQ>> contractors;
        if (work) contractors.push_back(std::make_unique<CountingContractorQ>(calls));
        IcpConfig config;
        config.maxIterations = 0;
        config.maxContractors = 0;
        const auto result = IcpEngineQ{}.run(contractors, WatcherMap{}, box, config);
        CAPTURE(work);
        CHECK(calls == 0);
        CHECK(result.status == IcpStatus::Conflict);
        CHECK(result.conflict.has_value());
        if (!result.conflict) continue;
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), lower)
              != result.conflict->clause.end());
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), upper)
              != result.conflict->clause.end());
    }
}

TEST_CASE("ICP-Q reasons: a final-budget empty update is a justified conflict") {
    for (bool watched : {false, true}) {
        int calls = 0;
        ReasonedBoxQ box;
        const auto lower = SatLit::positive(1), upper = SatLit::negative(2);
        box.set("x", {IntervalQ{2, 3}, {lower}});
        std::vector<std::unique_ptr<ContractorQ>> contractors;
        contractors.push_back(std::make_unique<EmptyingContractorQ>(calls));
        WatcherMap watchers;
        if (watched) watchers.addWatcher("x", 0);
        IcpConfig config;
        config.maxIterations = 1;
        config.maxContractors = 1;
        const auto result = IcpEngineQ{}.run(contractors, watchers, box, config);
        CAPTURE(watched);
        CHECK(calls == 1);
        CHECK(box.isEmpty());
        CHECK(result.status == IcpStatus::Conflict);
        CHECK(result.conflict.has_value());
        if (!result.conflict) continue;
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), lower)
              != result.conflict->clause.end());
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), upper)
              != result.conflict->clause.end());
    }
}
