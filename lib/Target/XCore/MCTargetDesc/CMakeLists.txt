if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support XCoreAsmPrinter XCoreInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMXCoreDesc
  XCoreMCTargetDesc.cpp
  XCoreMCAsmInfo.cpp
  )
