if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC NVPTXAsmPrinter NVPTXInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMNVPTXDesc
  NVPTXMCAsmInfo.cpp
  NVPTXMCTargetDesc.cpp
  )
