if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMX86Utils
  X86ShuffleDecode.cpp
  )
