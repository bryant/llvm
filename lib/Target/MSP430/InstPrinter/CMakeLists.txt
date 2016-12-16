if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(PPP)
add_llvm_library(LLVMMSP430AsmPrinter
  MSP430InstPrinter.cpp
  )
