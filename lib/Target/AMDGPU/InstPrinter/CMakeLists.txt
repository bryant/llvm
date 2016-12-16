if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support AMDGPUUtils)
endif(PPP)
add_llvm_library(LLVMAMDGPUAsmPrinter
  AMDGPUInstPrinter.cpp
  )

add_dependencies(LLVMAMDGPUAsmPrinter LLVMAMDGPUUtils)
