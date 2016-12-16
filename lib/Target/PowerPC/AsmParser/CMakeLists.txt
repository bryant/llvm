if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser PowerPCDesc PowerPCInfo Support)
endif(PPP)
add_llvm_library(LLVMPowerPCAsmParser
  PPCAsmParser.cpp
  )
