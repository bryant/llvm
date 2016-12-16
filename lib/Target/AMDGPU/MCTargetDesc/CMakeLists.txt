
if(PPP)
  set(LLVM_LINK_COMPONENTS MC AMDGPUAsmPrinter AMDGPUInfo AMDGPUUtils Support)
endif(PPP)
add_llvm_library(LLVMAMDGPUDesc
  AMDGPUAsmBackend.cpp
  AMDGPUELFObjectWriter.cpp
  AMDGPUELFStreamer.cpp
  AMDGPUMCCodeEmitter.cpp
  AMDGPUMCTargetDesc.cpp
  AMDGPUMCAsmInfo.cpp
  AMDGPURuntimeMD.cpp
  AMDGPUTargetStreamer.cpp
  R600MCCodeEmitter.cpp
  SIMCCodeEmitter.cpp
  )
