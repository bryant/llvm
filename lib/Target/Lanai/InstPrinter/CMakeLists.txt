if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS LanaiInfo MC Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLanaiInstPrinter
  LanaiInstPrinter.cpp
  )
