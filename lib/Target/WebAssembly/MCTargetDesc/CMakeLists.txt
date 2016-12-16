if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support WebAssemblyAsmPrinter WebAssemblyInfo)
endif(PPP)
add_llvm_library(LLVMWebAssemblyDesc
  WebAssemblyAsmBackend.cpp
  WebAssemblyELFObjectWriter.cpp
  WebAssemblyMCAsmInfo.cpp
  WebAssemblyMCCodeEmitter.cpp
  WebAssemblyMCTargetDesc.cpp
  WebAssemblyTargetStreamer.cpp
)
