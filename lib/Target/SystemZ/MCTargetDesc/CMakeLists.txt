if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC Support SystemZAsmPrinter SystemZInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMSystemZDesc
  SystemZMCAsmBackend.cpp
  SystemZMCAsmInfo.cpp
  SystemZMCCodeEmitter.cpp
  SystemZMCObjectWriter.cpp
  SystemZMCTargetDesc.cpp
  )
