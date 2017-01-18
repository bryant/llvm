add_llvm_library(LLVMHexagonDisassembler
  HexagonDisassembler.cpp

  LINK_COMPONENTS
    HexagonDesc
    HexagonInfo
    MC
    MCDisassembler
    Support

)
