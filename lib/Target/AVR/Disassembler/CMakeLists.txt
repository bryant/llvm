if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler AVRInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAVRDisassembler
  AVRDisassembler.cpp
)

