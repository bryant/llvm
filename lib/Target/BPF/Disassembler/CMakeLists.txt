if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler BPFInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMBPFDisassembler
  BPFDisassembler.cpp
)

