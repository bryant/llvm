add_llvm_library(LLVMXCoreDisassembler
  XCoreDisassembler.cpp

  LINK_COMPONENTS
    MCDisassembler
    Support
    XCoreInfo
)
