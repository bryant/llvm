if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support)
endif(PPP)
add_llvm_library(LLVMMCDisassembler
  Disassembler.cpp
  MCDisassembler.cpp
  MCExternalSymbolizer.cpp
  MCRelocationInfo.cpp
  MCSymbolizer.cpp
  )
