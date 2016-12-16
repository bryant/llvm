if(PPP)
  set(LLVM_LINK_COMPONENTS MC NVPTXAsmPrinter NVPTXInfo Support)
endif(PPP)
add_llvm_library(LLVMNVPTXDesc
  NVPTXMCAsmInfo.cpp
  NVPTXMCTargetDesc.cpp
  )
