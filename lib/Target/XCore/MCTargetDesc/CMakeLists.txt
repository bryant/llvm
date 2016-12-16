if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support XCoreAsmPrinter XCoreInfo)
endif(PPP)
add_llvm_library(LLVMXCoreDesc
  XCoreMCTargetDesc.cpp
  XCoreMCAsmInfo.cpp
  )
