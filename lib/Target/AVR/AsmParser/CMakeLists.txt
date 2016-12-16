if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser AVRDesc AVRInfo Support)
endif(PPP)
add_llvm_library(LLVMAVRAsmParser
  AVRAsmParser.cpp
)
