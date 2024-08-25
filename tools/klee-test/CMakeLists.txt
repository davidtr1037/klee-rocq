add_executable(klee-test
  main.cpp
)

set(KLEE_LIBS
  kleeCore
  kleeCoq
)

target_link_libraries(klee-test ${KLEE_LIBS})
target_include_directories(klee-test PRIVATE ${KLEE_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS})
target_compile_options(klee-test PRIVATE ${KLEE_COMPONENT_CXX_FLAGS})
target_compile_definitions(klee-test PRIVATE ${KLEE_COMPONENT_CXX_DEFINES})


install(TARGETS klee-test RUNTIME DESTINATION bin)

# The KLEE binary depends on the runtimes
add_dependencies(klee-test BuildKLEERuntimes)
