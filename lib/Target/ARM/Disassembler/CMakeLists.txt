add_llvm_library(LLVMARMDisassembler
  ARMDisassembler.cpp

  LINK_COMPONENTS
    ARMDesc
    ARMInfo
    MCDisassembler
    Support
)
