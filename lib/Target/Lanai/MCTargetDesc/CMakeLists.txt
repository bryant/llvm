if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS LanaiInfo LanaiInstPrinter MC MCDisassembler Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLanaiDesc
  LanaiAsmBackend.cpp
  LanaiELFObjectWriter.cpp
  LanaiMCAsmInfo.cpp
  LanaiMCCodeEmitter.cpp
  LanaiMCExpr.cpp
  LanaiMCTargetDesc.cpp
)
