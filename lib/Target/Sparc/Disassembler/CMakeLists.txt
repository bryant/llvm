add_llvm_library(LLVMSparcDisassembler
  SparcDisassembler.cpp

  LINK_COMPONENTS
    MCDisassembler
    SparcInfo
    Support
)
