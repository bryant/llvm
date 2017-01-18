add_llvm_library(LLVMMipsAsmParser
  MipsAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    MipsDesc
    MipsInfo
    Support

)
