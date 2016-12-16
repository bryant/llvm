if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(PPP)
add_llvm_library(LLVMSystemZAsmPrinter
  SystemZInstPrinter.cpp
  )
