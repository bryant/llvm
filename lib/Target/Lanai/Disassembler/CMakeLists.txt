if(PPP)
  set(LLVM_LINK_COMPONENTS LanaiDesc LanaiInfo MC MCDisassembler Support)
endif(PPP)
add_llvm_library(LLVMLanaiDisassembler
  LanaiDisassembler.cpp
  )
