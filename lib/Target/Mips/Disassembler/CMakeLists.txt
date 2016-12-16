if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler MipsInfo Support)
endif(PPP)
add_llvm_library(LLVMMipsDisassembler
  MipsDisassembler.cpp
  )
