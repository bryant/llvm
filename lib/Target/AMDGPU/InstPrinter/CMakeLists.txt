if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support AMDGPUUtils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAMDGPUAsmPrinter
  AMDGPUInstPrinter.cpp
  )

add_dependencies(LLVMAMDGPUAsmPrinter LLVMAMDGPUUtils)
