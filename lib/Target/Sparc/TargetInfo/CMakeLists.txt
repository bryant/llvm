if(PPP)
  set(LLVM_LINK_COMPONENTS Support)
endif(PPP)
add_llvm_library(LLVMSparcInfo
  SparcTargetInfo.cpp
  )
