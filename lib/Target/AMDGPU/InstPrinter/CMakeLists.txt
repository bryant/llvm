add_llvm_library(LLVMAMDGPUAsmPrinter
  AMDGPUInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support
    AMDGPUUtils

)

add_dependencies(LLVMAMDGPUAsmPrinter LLVMAMDGPUUtils)
