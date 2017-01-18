add_llvm_library(LLVMSystemZAsmParser
  SystemZAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    Support
    SystemZDesc
    SystemZInfo

)
