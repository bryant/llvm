if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser Support SystemZDesc SystemZInfo)
endif(PPP)
add_llvm_library(LLVMSystemZAsmParser
  SystemZAsmParser.cpp
  )
