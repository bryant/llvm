add_llvm_library(LLVMWebAssemblyAsmPrinter
  WebAssemblyInstPrinter.cpp

  LINK_COMPONENTS
    MC
    Support

)
