add_llvm_library(LLVMAVRDisassembler
  AVRDisassembler.cpp

  LINK_COMPONENTS
    MCDisassembler
    AVRInfo
    Support
)

