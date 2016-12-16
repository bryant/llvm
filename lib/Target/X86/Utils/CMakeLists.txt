if(PPP)
  set(LLVM_LINK_COMPONENTS Core Support)
endif(PPP)
add_llvm_library(LLVMX86Utils
  X86ShuffleDecode.cpp
  )
