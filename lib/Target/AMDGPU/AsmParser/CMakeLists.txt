if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser AMDGPUDesc AMDGPUInfo AMDGPUUtils Support)
endif(PPP)
add_llvm_library(LLVMAMDGPUAsmParser
  AMDGPUAsmParser.cpp
  )

add_dependencies(LLVMAMDGPUAsmParser LLVMAMDGPUUtils)
