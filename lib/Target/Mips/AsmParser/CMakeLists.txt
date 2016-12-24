if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser MipsDesc MipsInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMMipsAsmParser
  MipsAsmParser.cpp
  )
