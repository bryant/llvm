if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(PPP)
add_llvm_library(LLVMARMAsmPrinter
  ARMInstPrinter.cpp
  )
