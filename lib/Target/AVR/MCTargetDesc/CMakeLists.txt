add_llvm_library(LLVMAVRDesc
  AVRAsmBackend.cpp
  AVRELFObjectWriter.cpp
  AVRELFStreamer.cpp
  AVRMCAsmInfo.cpp
  AVRMCCodeEmitter.cpp
  AVRMCExpr.cpp
  AVRMCTargetDesc.cpp
  AVRTargetStreamer.cpp

  LINK_COMPONENTS
    MC
    AVRAsmPrinter
    AVRInfo
    Support
)

add_dependencies(LLVMAVRDesc AVRCommonTableGen)

