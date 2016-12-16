if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser SparcDesc SparcInfo Support)
endif(PPP)
add_llvm_library(LLVMSparcAsmParser
  SparcAsmParser.cpp
  )
