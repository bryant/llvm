if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC PowerPCAsmPrinter PowerPCInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMPowerPCDesc
  PPCAsmBackend.cpp
  PPCMCTargetDesc.cpp
  PPCMCAsmInfo.cpp
  PPCMCCodeEmitter.cpp
  PPCMCExpr.cpp
  PPCPredicates.cpp
  PPCMachObjectWriter.cpp
  PPCELFObjectWriter.cpp
  )
