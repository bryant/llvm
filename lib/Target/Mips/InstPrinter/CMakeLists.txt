add_llvm_library(LLVMMipsAsmPrinter
  MipsInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support
)
