if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler SparcInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSparcDisassembler
  SparcDisassembler.cpp
  )
