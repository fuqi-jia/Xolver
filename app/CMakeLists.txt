cmake_minimum_required(VERSION 3.16)

add_executable(xolver-cli
    main.cpp
)

find_package(Threads REQUIRED)
target_link_libraries(xolver-cli PRIVATE xolver_core Threads::Threads)

# If the closed pro lib was built, link it with --whole-archive so its static
# self-registration objects (which nothing references directly) are retained.
if(TARGET xolver_pro)
    target_link_libraries(xolver-cli PRIVATE
        -Wl,--whole-archive xolver_pro -Wl,--no-whole-archive)
endif()

set_target_properties(xolver-cli PROPERTIES
    OUTPUT_NAME xolver
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)
