if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser MipsDesc MipsInfo Support)
endif(PPP)
add_llvm_library(LLVMMipsAsmParser
  MipsAsmParser.cpp
  )
