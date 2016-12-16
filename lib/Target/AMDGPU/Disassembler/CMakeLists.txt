include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS AMDGPUDesc AMDGPUInfo AMDGPUUtils MC MCDisassembler Support)
endif(PPP)
add_llvm_library(LLVMAMDGPUDisassembler
  AMDGPUDisassembler.cpp
  )

add_dependencies(LLVMAMDGPUDisassembler AMDGPUCommonTableGen LLVMAMDGPUUtils)
