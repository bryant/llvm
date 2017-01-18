add_llvm_library(LLVMNVPTXAsmPrinter
  NVPTXInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
