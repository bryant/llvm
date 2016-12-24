if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC SparcAsmPrinter SparcInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSparcDesc
  SparcAsmBackend.cpp
  SparcELFObjectWriter.cpp
  SparcMCAsmInfo.cpp
  SparcMCCodeEmitter.cpp
  SparcMCTargetDesc.cpp
  SparcMCExpr.cpp
  SparcTargetStreamer.cpp
  )
