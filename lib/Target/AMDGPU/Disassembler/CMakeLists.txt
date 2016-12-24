include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS AMDGPUDesc AMDGPUInfo AMDGPUUtils MC MCDisassembler Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAMDGPUDisassembler
  AMDGPUDisassembler.cpp
  )

add_dependencies(LLVMAMDGPUDisassembler AMDGPUCommonTableGen LLVMAMDGPUUtils)
