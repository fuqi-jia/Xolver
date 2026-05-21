cmake_minimum_required(VERSION 3.16)

# ---------------------------------------------------------------------------
# Testing framework: doctest (header-only, fetched)
# ---------------------------------------------------------------------------
# Use local doctest if available (from prior build), otherwise fetch
if(EXISTS "${CMAKE_BINARY_DIR}/_deps/doctest-src/doctest/doctest.h")
    add_library(doctest INTERFACE)
    target_include_directories(doctest INTERFACE "${CMAKE_BINARY_DIR}/_deps/doctest-src")
    add_library(doctest::doctest ALIAS doctest)
else()
    include(FetchContent)
    FetchContent_Declare(
        doctest
        GIT_REPOSITORY https://github.com/doctest/doctest.git
        GIT_TAG v2.4.11
        GIT_SHALLOW TRUE
    )
    FetchContent_MakeAvailable(doctest)
endif()

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
            ${GMP_LIBRARIES}
            gmpxx
    )
    target_include_directories(nlcolver_unit_tests PRIVATE ${CMAKE_SOURCE_DIR}/src)
    add_test(NAME unit COMMAND nlcolver_unit_tests)
    set_tests_properties(unit PROPERTIES LABELS "unit")
endif()

# ---------------------------------------------------------------------------
# Regression tests — SMT-LIB files driven by tools/run_regression.py.
# Each logic gets its own CTest entry + label so users can run e.g.
#     ctest -L euf            # all EUF regression
#     ctest -L regression     # everything
# UNEXPECTED_FAIL counts non-zero exit; KNOWN_FAIL (tagged via
#     (set-info :nlcolver-expected known-fail) ) does not.
# ---------------------------------------------------------------------------
find_package(Python3 COMPONENTS Interpreter)
if(Python3_FOUND)
    set(REGRESSION_LOGICS
        bool euf lia lira lra nia nira nra uflia uflra ufnia ufnra)

    foreach(logic ${REGRESSION_LOGICS})
        if(IS_DIRECTORY "${CMAKE_SOURCE_DIR}/tests/regression/${logic}")
            add_test(
                NAME regression-${logic}
                COMMAND ${Python3_EXECUTABLE}
                    ${CMAKE_SOURCE_DIR}/tools/run_regression.py
                    --root ${CMAKE_SOURCE_DIR}/tests/regression
                    --logic ${logic}
                    --solver $<TARGET_FILE:nlcolver-cli>
                    --timeout 20
                    -j 2
            )
            set_tests_properties(regression-${logic} PROPERTIES
                LABELS "regression;${logic}")
        endif()
    endforeach()
endif()
