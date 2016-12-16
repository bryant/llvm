if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler PowerPCInfo Support)
endif(PPP)
add_llvm_library(LLVMPowerPCDisassembler
  PPCDisassembler.cpp
  )
