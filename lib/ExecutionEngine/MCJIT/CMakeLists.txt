if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core ExecutionEngine Object RuntimeDyld Support Target)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMMCJIT
  MCJIT.cpp

  DEPENDS
  intrinsics_gen
  )
