add_llvm_library(LLVMSystemZDisassembler
  SystemZDisassembler.cpp

  LINK_COMPONENTS
    MC
    MCDisassembler
    Support
    SystemZDesc
    SystemZInfo
)
