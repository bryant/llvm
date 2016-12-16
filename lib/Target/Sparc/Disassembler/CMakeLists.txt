if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler SparcInfo Support)
endif(PPP)
add_llvm_library(LLVMSparcDisassembler
  SparcDisassembler.cpp
  )
