if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC BPFAsmPrinter BPFInfo Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMBPFDesc
  BPFMCTargetDesc.cpp
  BPFAsmBackend.cpp
  BPFMCCodeEmitter.cpp
  BPFELFObjectWriter.cpp
  )
