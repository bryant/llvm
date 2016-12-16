if(PPP)
  set(LLVM_LINK_COMPONENTS MC Support SystemZAsmPrinter SystemZInfo)
endif(PPP)
add_llvm_library(LLVMSystemZDesc
  SystemZMCAsmBackend.cpp
  SystemZMCAsmInfo.cpp
  SystemZMCCodeEmitter.cpp
  SystemZMCObjectWriter.cpp
  SystemZMCTargetDesc.cpp
  )
