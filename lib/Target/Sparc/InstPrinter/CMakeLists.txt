add_llvm_library(LLVMSparcAsmPrinter
  SparcInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
