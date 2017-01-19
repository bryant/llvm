add_llvm_library(LLVMSystemZAsmPrinter
  SystemZInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support
)
