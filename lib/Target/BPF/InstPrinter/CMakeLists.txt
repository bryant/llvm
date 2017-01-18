add_llvm_library(LLVMBPFAsmPrinter
  BPFInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
