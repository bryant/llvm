if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core ExecutionEngine Object RuntimeDyld Support TransformUtils)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMOrcJIT
  ExecutionUtils.cpp
  IndirectionUtils.cpp
  NullResolver.cpp
  OrcABISupport.cpp
  OrcCBindings.cpp
  OrcError.cpp
  OrcMCJITReplacement.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/ExecutionEngine/Orc

  DEPENDS
  intrinsics_gen
  )
