if(PPP)
  set(LLVM_LINK_COMPONENTS MC MipsAsmPrinter MipsInfo Support)
endif(PPP)
add_llvm_library(LLVMMipsDesc
  MipsABIInfo.cpp
  MipsABIFlagsSection.cpp
  MipsAsmBackend.cpp
  MipsELFObjectWriter.cpp
  MipsELFStreamer.cpp
  MipsMCAsmInfo.cpp
  MipsMCCodeEmitter.cpp
  MipsMCExpr.cpp
  MipsMCTargetDesc.cpp
  MipsNaClELFStreamer.cpp
  MipsOptionRecord.cpp
  MipsTargetStreamer.cpp
  )
