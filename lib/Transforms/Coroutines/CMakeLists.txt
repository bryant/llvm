add_llvm_library(LLVMCoroutines
  Coroutines.cpp
  CoroCleanup.cpp
  CoroEarly.cpp
  CoroElide.cpp
  CoroFrame.cpp
  CoroSplit.cpp  

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
    Analysis
    Core
    ipo
    ScalarOpts
    Support
    TransformUtils
)
