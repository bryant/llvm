if(PPP)
  set(LLVM_LINK_COMPONENTS HexagonDesc HexagonInfo MC MCDisassembler Support)
endif(PPP)
add_llvm_library(LLVMHexagonDisassembler
  HexagonDisassembler.cpp
  )
