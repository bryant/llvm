if(PPP)
  set(LLVM_LINK_COMPONENTS MC BPFAsmPrinter BPFInfo Support)
endif(PPP)
add_llvm_library(LLVMBPFDesc
  BPFMCTargetDesc.cpp
  BPFAsmBackend.cpp
  BPFMCCodeEmitter.cpp
  BPFELFObjectWriter.cpp
  )
