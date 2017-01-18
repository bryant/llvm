add_llvm_library(LLVMPowerPCAsmParser
  PPCAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    PowerPCDesc
    PowerPCInfo
    Support

)
