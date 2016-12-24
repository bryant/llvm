if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS ARMDesc ARMInfo MC MCParser Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMARMAsmParser
  ARMAsmParser.cpp
  )
