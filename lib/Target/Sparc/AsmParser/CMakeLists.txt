add_llvm_library(LLVMSparcAsmParser
  SparcAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    SparcDesc
    SparcInfo
    Support

)
