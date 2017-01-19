add_llvm_library(LLVMLanaiAsmPrinter
  LanaiInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support
)
