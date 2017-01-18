add_llvm_library(LLVMNVPTXDesc
  NVPTXMCAsmInfo.cpp
  NVPTXMCTargetDesc.cpp

  LINK_COMPONENTS
    MC
    NVPTXAsmPrinter
    NVPTXInfo
    Support

)
