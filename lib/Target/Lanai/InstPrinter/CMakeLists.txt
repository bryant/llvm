add_llvm_library(LLVMLanaiInstPrinter
  LanaiInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support
)
