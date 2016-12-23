if(PPP)
  set(LLVM_LINK_COMPONENTS MC RISCVInfo Support)
endif(PPP)
add_llvm_library(LLVMRISCVDesc
  RISCVAsmBackend.cpp
  RISCVELFObjectWriter.cpp
  RISCVMCAsmInfo.cpp
  RISCVMCTargetDesc.cpp
  RISCVMCCodeEmitter.cpp
)
