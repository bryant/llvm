if(PPP)
  set(LLVM_LINK_COMPONENTS DebugInfoDWARF DebugInfoPDB Object Support)
endif(PPP)
add_llvm_library(LLVMSymbolize
  DIPrinter.cpp
  SymbolizableObjectFile.cpp
  Symbolize.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/DebugInfo/Symbolize
  )
