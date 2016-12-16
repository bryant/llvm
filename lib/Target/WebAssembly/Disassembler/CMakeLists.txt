if(PPP)
  set(LLVM_LINK_COMPONENTS MCDisassembler WebAssemblyInfo Support)
endif(PPP)
add_llvm_library(LLVMWebAssemblyDisassembler
  WebAssemblyDisassembler.cpp
  )
