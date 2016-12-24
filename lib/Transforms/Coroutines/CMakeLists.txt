if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Analysis Core IPO ScalarOpts Support TransformUtils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMCoroutines
  Coroutines.cpp
  CoroCleanup.cpp
  CoroEarly.cpp
  CoroElide.cpp
  CoroFrame.cpp
  CoroSplit.cpp  

  DEPENDS
  intrinsics_gen
  )
