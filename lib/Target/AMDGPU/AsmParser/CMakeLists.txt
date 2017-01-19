add_llvm_library(LLVMAMDGPUAsmParser
  AMDGPUAsmParser.cpp

  LINK_COMPONENTS
    MC
    MCParser
    AMDGPUDesc
    AMDGPUInfo
    AMDGPUUtils
    Support
)

add_dependencies(LLVMAMDGPUAsmParser LLVMAMDGPUUtils)
