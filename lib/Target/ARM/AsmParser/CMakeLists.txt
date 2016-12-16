if(PPP)
  set(LLVM_LINK_COMPONENTS ARMDesc ARMInfo MC MCParser Support)
endif(PPP)
add_llvm_library(LLVMARMAsmParser
  ARMAsmParser.cpp
  )
