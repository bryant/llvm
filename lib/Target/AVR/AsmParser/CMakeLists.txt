add_llvm_library(LLVMAVRAsmParser
  AVRAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    AVRDesc
    AVRInfo
    Support
)
