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
    add_executable(xolver_unit_tests ${UNIT_TEST_SOURCES})
    target_link_libraries(xolver_unit_tests
        PRIVATE
            xolver_core
            doctest::doctest
            ${GMP_LIBRARIES}
            gmpxx
    )
    target_include_directories(xolver_unit_tests PRIVATE ${CMAKE_SOURCE_DIR}/src)
    add_test(NAME unit COMMAND xolver_unit_tests)
    set_tests_properties(unit PROPERTIES LABELS "unit")
endif()

add_executable(xolver_checker_tests checker/main.cpp)
target_link_libraries(xolver_checker_tests PRIVATE xolver_checkers)
add_test(NAME standalone-evidence COMMAND xolver_checker_tests)
set_tests_properties(standalone-evidence PROPERTIES LABELS "soundness;architecture")

if(XOLVER_BUILD_TOOLS)
    # Export original SL formulas and concrete model pins for external checking.
    add_executable(xolver_sl_cases sl_cases.cpp)
    target_link_libraries(xolver_sl_cases PRIVATE xolver_core gmpxx)
    add_executable(xolver_sv_cases sv_cases.cpp)
    target_link_libraries(xolver_sv_cases PRIVATE xolver_core gmpxx)
endif()

# ---------------------------------------------------------------------------
# Regression tests — SMT-LIB files driven by tools/regression/run_regression.py.
# Each logic gets its own CTest entry + label so users can run e.g.
#     ctest -L euf            # all EUF regression
#     ctest -L regression     # everything
# UNEXPECTED_FAIL counts non-zero exit; KNOWN_FAIL (tagged via
#     (set-info :xolver-expected known-fail) ) does not.
# ---------------------------------------------------------------------------
find_package(Python3 COMPONENTS Interpreter)
if(Python3_FOUND AND XOLVER_BUILD_TOOLS)
    # Register every regression directory, including newly added theories.
    # The previous manual list silently omitted SL and UFDTLIA from CTest.
    file(GLOB REGRESSION_DIRECTORIES CONFIGURE_DEPENDS LIST_DIRECTORIES true
        "${CMAKE_SOURCE_DIR}/tests/regression/*")
    foreach(directory ${REGRESSION_DIRECTORIES})
        get_filename_component(logic "${directory}" NAME)
        if(IS_DIRECTORY "${CMAKE_SOURCE_DIR}/tests/regression/${logic}")
            add_test(
                NAME regression-${logic}
                COMMAND ${Python3_EXECUTABLE}
                    ${CMAKE_SOURCE_DIR}/tools/regression/run_regression.py
                    --root ${CMAKE_SOURCE_DIR}/tests/regression
                    --logic ${logic}
                    --solver $<TARGET_FILE:xolver-cli>
                    --timeout 20
                    -j 2
            )
            set_tests_properties(regression-${logic} PROPERTIES
                LABELS "regression;${logic}")
        endif()
    endforeach()
    add_test(NAME known-gaps
        COMMAND ${Python3_EXECUTABLE}
            ${CMAKE_SOURCE_DIR}/tools/regression/run_regression.py
            --root ${CMAKE_SOURCE_DIR}/tests/known_gaps
            --solver $<TARGET_FILE:xolver-cli> --allow-unknown --timeout 20 -j 2)
    set_tests_properties(known-gaps PROPERTIES LABELS "soundness;known-gaps")
endif()

if(Python3_FOUND)
    add_test(NAME architecture
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/tools/governance/architecture.py)
    add_test(NAME regression-harness
        COMMAND ${Python3_EXECUTABLE} -m unittest discover
            -s ${CMAKE_SOURCE_DIR}/tests/tools -p test_*.py)
    set_tests_properties(regression-harness PROPERTIES LABELS "soundness;tools")
    if(XOLVER_BUILD_TOOLS)
        set_tests_properties(regression-harness PROPERTIES
            ENVIRONMENT "XOLVER_TEST_SOLVER=$<TARGET_FILE:xolver-cli>")
    endif()
endif()
