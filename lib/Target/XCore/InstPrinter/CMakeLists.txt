add_llvm_library(LLVMXCoreAsmPrinter
  XCoreInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
