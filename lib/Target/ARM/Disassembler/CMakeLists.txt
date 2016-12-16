if(PPP)
  set(LLVM_LINK_COMPONENTS ARMDesc ARMInfo MCDisassembler Support)
endif(PPP)
add_llvm_library(LLVMARMDisassembler
  ARMDisassembler.cpp
  )
