add_llvm_library(LLVMARMAsmPrinter
  ARMInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
