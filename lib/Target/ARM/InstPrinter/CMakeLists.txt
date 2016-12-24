if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMARMAsmPrinter
  ARMInstPrinter.cpp
  )
