if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler Support XCoreInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMXCoreDisassembler
  XCoreDisassembler.cpp
  )
