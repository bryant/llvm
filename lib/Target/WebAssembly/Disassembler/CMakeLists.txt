if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MCDisassembler WebAssemblyInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMWebAssemblyDisassembler
  WebAssemblyDisassembler.cpp
  )
