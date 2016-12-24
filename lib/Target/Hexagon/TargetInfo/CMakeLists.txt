if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMHexagonInfo
  HexagonTargetInfo.cpp
  )
