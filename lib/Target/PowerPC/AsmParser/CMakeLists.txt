if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser PowerPCDesc PowerPCInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMPowerPCAsmParser
  PPCAsmParser.cpp
  )
