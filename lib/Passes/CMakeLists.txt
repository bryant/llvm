add_llvm_library(LLVMPasses
  PassBuilder.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Passes

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
    Analysis
    CodeGen
    Core
    ipo
    InstCombine
    ScalarOpts
    Support
    TransformUtils
    Vectorize
    Instrumentation

)
