if(PPP)
  set(LLVM_LINK_COMPONENTS Core MC Support)
endif(PPP)
add_llvm_library(LLVMAMDGPUUtils
  AMDGPUBaseInfo.cpp
  AMDKernelCodeTUtils.cpp
  AMDGPUAsmUtils.cpp
  )
