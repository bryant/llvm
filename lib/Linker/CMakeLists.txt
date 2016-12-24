if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core Support TransformUtils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLinker
  IRMover.cpp
  LinkModules.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Linker

  DEPENDS
  intrinsics_gen
  )
