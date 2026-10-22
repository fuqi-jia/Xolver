cmake_minimum_required(VERSION 3.16)

add_executable(xolver-cli
    main.cpp
)

find_package(Threads REQUIRED)
target_link_libraries(xolver-cli PRIVATE xolver_core Threads::Threads)

set_target_properties(xolver-cli PROPERTIES
    OUTPUT_NAME xolver
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)
