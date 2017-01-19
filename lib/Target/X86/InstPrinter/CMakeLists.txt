add_llvm_library(LLVMX86AsmPrinter
  X86ATTInstPrinter.cpp
  X86IntelInstPrinter.cpp
  X86InstComments.cpp

  LINK_COMPONENTS
    MC
    Support
    X86Utils
)
