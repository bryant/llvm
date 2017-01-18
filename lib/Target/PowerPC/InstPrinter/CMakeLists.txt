add_llvm_library(LLVMPowerPCAsmPrinter
  PPCInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
