add_llvm_library(LLVMLanaiDesc
  LanaiAsmBackend.cpp
  LanaiELFObjectWriter.cpp
  LanaiMCAsmInfo.cpp
  LanaiMCCodeEmitter.cpp
  LanaiMCExpr.cpp
  LanaiMCTargetDesc.cpp

  LINK_COMPONENTS
    LanaiInfo
    LanaiInstPrinter
    MC
    MCDisassembler
    Support

)
