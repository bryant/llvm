if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS LanaiDesc LanaiInfo MC MCDisassembler Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLanaiDisassembler
  LanaiDisassembler.cpp
  )
