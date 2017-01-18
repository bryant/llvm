add_llvm_library(LLVMX86Utils
  X86ShuffleDecode.cpp

  LINK_COMPONENTS
    Core
    Support

)
