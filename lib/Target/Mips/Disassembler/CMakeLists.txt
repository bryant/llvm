if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler MipsInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMMipsDisassembler
  MipsDisassembler.cpp
  )
