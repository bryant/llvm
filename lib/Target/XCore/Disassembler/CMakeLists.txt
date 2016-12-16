if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler Support XCoreInfo)
endif(PPP)
add_llvm_library(LLVMXCoreDisassembler
  XCoreDisassembler.cpp
  )
