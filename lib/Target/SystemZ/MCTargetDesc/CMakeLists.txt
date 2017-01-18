add_llvm_library(LLVMSystemZDesc
  SystemZMCAsmBackend.cpp
  SystemZMCAsmInfo.cpp
  SystemZMCCodeEmitter.cpp
  SystemZMCObjectWriter.cpp
  SystemZMCTargetDesc.cpp

  LINK_COMPONENTS
    MC
    Support
    SystemZAsmPrinter
    SystemZInfo

)
