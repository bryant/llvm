if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser AMDGPUDesc AMDGPUInfo AMDGPUUtils Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAMDGPUAsmParser
  AMDGPUAsmParser.cpp
  )

add_dependencies(LLVMAMDGPUAsmParser LLVMAMDGPUUtils)
