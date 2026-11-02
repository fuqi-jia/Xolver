#include <doctest/doctest.h>
#include "ir/AssertionSnapshot.h"

using namespace xolver;

namespace {
ExprId boolean(NativeTerms& terms, const char* name) {
    if (terms.boolSortId() == NullSort) {
        const auto sort = terms.allocateSortId();
        terms.registerSort(sort, SortKind::Bool); terms.setBoolSortId(sort);
    }
    return terms.add({Kind::Variable, terms.boolSortId(), {},
                      Payload(std::string(name))});
}
}

TEST_CASE("AssertionSnapshot: exact assertion roots survive append and restore") {
    NativeTerms terms;
    const auto first = boolean(terms, "first");
    terms.addAssertion(first);
    const AssertionSnapshot saved(terms);
    CHECK(saved.matches(terms));
    const auto second = boolean(terms, "second");
    CHECK(saved.matches(terms)); // Unasserted indexed terms are irrelevant.
    auto roots = terms.getScopedAssertions();
    terms.addAssertion(second);
    CHECK_FALSE(saved.matches(terms));
    terms.restoreAssertions(std::move(roots));
    CHECK(saved.matches(terms));
    terms.replaceAssertions({second});
    CHECK_FALSE(saved.matches(terms)); // Same count, different obligation.
    terms.clearAssertions();
    CHECK_FALSE(saved.matches(terms));
}

TEST_CASE("AssertionSnapshot: pop withdraws scoped assumptions") {
    NativeTerms terms;
    const auto root = boolean(terms, "root");
    terms.addAssertion(root);
    const AssertionSnapshot outer(terms);
    terms.pushScope();
    terms.addAssertion(root);
    const AssertionSnapshot inner(terms);
    CHECK_FALSE(outer.matches(terms));
    terms.popScope();
    CHECK(outer.matches(terms));
    CHECK_FALSE(inner.matches(terms));
}

TEST_CASE("AssertionSnapshot: replacing an index space cannot alias equal handles") {
    NativeTerms terms;
    terms.addAssertion(boolean(terms, "before"));
    const auto roots = terms.getScopedAssertions();
    const AssertionSnapshot old(terms);
    terms = NativeTerms();
    terms.addAssertion(boolean(terms, "after"));
    REQUIRE(roots == terms.getScopedAssertions());
    CHECK_FALSE(old.matches(terms));
    const AssertionSnapshot current(terms);
    NativeTerms copy(terms);
    CHECK_FALSE(current.matches(copy));
    NativeTerms moved(std::move(terms));
    CHECK(current.matches(moved));
    copy = moved;
    CHECK_FALSE(current.matches(copy));
}
