if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler AVRInfo Support)
endif(PPP)
add_llvm_library(LLVMAVRDisassembler
  AVRDisassembler.cpp
)

