if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC AVRAsmPrinter AVRInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAVRDesc
  AVRAsmBackend.cpp
  AVRELFObjectWriter.cpp
  AVRELFStreamer.cpp
  AVRMCAsmInfo.cpp
  AVRMCCodeEmitter.cpp
  AVRMCExpr.cpp
  AVRMCTargetDesc.cpp
  AVRTargetStreamer.cpp
)

add_dependencies(LLVMAVRDesc AVRCommonTableGen)

