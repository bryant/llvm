if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS ARMDesc ARMInfo MCDisassembler Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMARMDisassembler
  ARMDisassembler.cpp
  )
