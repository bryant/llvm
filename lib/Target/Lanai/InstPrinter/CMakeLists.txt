if(PPP)
  set(LLVM_LINK_COMPONENTS LanaiInfo MC Support)
endif(PPP)
add_llvm_library(LLVMLanaiInstPrinter
  LanaiInstPrinter.cpp
  )
