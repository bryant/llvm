add_llvm_library(LLVMMipsDisassembler
  MipsDisassembler.cpp

  LINK_COMPONENTS
    MCDisassembler
    MipsInfo
    Support

)
