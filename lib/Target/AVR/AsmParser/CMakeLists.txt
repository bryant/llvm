if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser AVRDesc AVRInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAVRAsmParser
  AVRAsmParser.cpp
)
