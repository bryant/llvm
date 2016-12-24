if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler PowerPCInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMPowerPCDisassembler
  PPCDisassembler.cpp
  )
