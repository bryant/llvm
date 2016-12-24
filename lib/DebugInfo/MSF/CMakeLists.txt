if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMDebugInfoMSF
  MappedBlockStream.cpp
  MSFBuilder.cpp
  MSFCommon.cpp
  MSFError.cpp
  StreamReader.cpp
  StreamWriter.cpp
  ADDITIONAL_HEADER_DIRS
  "${LLVM_MAIN_INCLUDE_DIR}/llvm/DebugInfo/MSF"
  )
