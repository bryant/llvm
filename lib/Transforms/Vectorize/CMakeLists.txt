if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Analysis Core Support TransformUtils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMVectorize
  BBVectorize.cpp
  LoadStoreVectorizer.cpp
  LoopVectorize.cpp
  SLPVectorizer.cpp
  Vectorize.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms

  DEPENDS
  intrinsics_gen
  )
