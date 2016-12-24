if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser SparcDesc SparcInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSparcAsmParser
  SparcAsmParser.cpp
  )
