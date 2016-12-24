if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support X86Utils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMX86AsmPrinter
  X86ATTInstPrinter.cpp
  X86IntelInstPrinter.cpp
  X86InstComments.cpp
  )
