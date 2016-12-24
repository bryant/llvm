if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCDisassembler Support SystemZDesc SystemZInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSystemZDisassembler
  SystemZDisassembler.cpp
  )
