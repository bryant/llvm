if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core MC Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAMDGPUUtils
  AMDGPUBaseInfo.cpp
  AMDKernelCodeTUtils.cpp
  AMDGPUAsmUtils.cpp
  )
