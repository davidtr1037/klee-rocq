#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_library(kleeCoq
    CoqLanguage.cpp
    ExprTranslation.cpp
    ModuleAssumptions.cpp
    Translation.cpp
)

llvm_config(kleeSupport "${USE_LLVM_SHARED}" support)

target_link_libraries(kleeCoq PRIVATE ${ZLIB_LIBRARIES} ${TCMALLOC_LIBRARIES})
target_include_directories(kleeCoq PRIVATE ${KLEE_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS} ${TCMALLOC_INCLUDE_DIR})
target_compile_options(kleeCoq PRIVATE ${KLEE_COMPONENT_CXX_FLAGS})
target_compile_definitions(kleeCoq PRIVATE ${KLEE_COMPONENT_CXX_DEFINES})
