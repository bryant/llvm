if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCDisassembler Support SystemZDesc SystemZInfo)
endif(PPP)
add_llvm_library(LLVMSystemZDisassembler
  SystemZDisassembler.cpp
  )
