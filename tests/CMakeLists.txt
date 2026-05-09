cmake_minimum_required(VERSION 3.16)

# ---------------------------------------------------------------------------
# Testing framework: doctest (header-only, fetched)
# ---------------------------------------------------------------------------
include(FetchContent)
FetchContent_Declare(
    doctest
    GIT_REPOSITORY https://github.com/doctest/doctest.git
    GIT_TAG v2.4.11
    GIT_SHALLOW TRUE
)
FetchContent_MakeAvailable(doctest)

# ---------------------------------------------------------------------------
# Unit tests
# ---------------------------------------------------------------------------
file(GLOB_RECURSE UNIT_TEST_SOURCES CONFIGURE_DEPENDS "unit/*.cpp")

if(UNIT_TEST_SOURCES)
    add_executable(nlcolver_unit_tests ${UNIT_TEST_SOURCES})
    target_link_libraries(nlcolver_unit_tests
        PRIVATE
            nlcolver_core
            doctest::doctest
    )
    target_include_directories(nlcolver_unit_tests PRIVATE ${CMAKE_SOURCE_DIR}/src)
    add_test(NAME unit COMMAND nlcolver_unit_tests)
endif()
