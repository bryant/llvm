add_llvm_library(LLVMXCoreDesc
  XCoreMCTargetDesc.cpp
  XCoreMCAsmInfo.cpp

  LINK_COMPONENTS
    MC
    Support
    XCoreAsmPrinter
    XCoreInfo
)
