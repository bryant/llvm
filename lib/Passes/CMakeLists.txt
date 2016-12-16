if(PPP)
  set(LLVM_LINK_COMPONENTS Analysis CodeGen Core IPO InstCombine Scalar Support TransformUtils Vectorize Instrumentation)
endif(PPP)
add_llvm_library(LLVMPasses
  PassBuilder.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Passes

  DEPENDS
  intrinsics_gen
  )
