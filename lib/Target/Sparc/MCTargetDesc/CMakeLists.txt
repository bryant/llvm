if(PPP)
  set(LLVM_LINK_COMPONENTS MC SparcAsmPrinter SparcInfo Support)
endif(PPP)
add_llvm_library(LLVMSparcDesc
  SparcAsmBackend.cpp
  SparcELFObjectWriter.cpp
  SparcMCAsmInfo.cpp
  SparcMCCodeEmitter.cpp
  SparcMCTargetDesc.cpp
  SparcMCExpr.cpp
  SparcTargetStreamer.cpp
  )
