if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC RISCVInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMRISCVDesc
  RISCVAsmBackend.cpp
  RISCVELFObjectWriter.cpp
  RISCVMCAsmInfo.cpp
  RISCVMCTargetDesc.cpp
  RISCVMCCodeEmitter.cpp
)
