add_llvm_library(LLVMPowerPCDisassembler
  PPCDisassembler.cpp

  LINK_COMPONENTS
    MCDisassembler
    PowerPCInfo
    Support
)
