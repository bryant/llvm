add_llvm_library(LLVMLanaiDisassembler
  LanaiDisassembler.cpp

  LINK_COMPONENTS
    LanaiDesc
    LanaiInfo
    MC
    MCDisassembler
    Support

)
