if(PPP)
  set(LLVM_LINK_COMPONENTS Core Object ProfileData Support)
endif(PPP)
add_llvm_library(LLVMCoverage
  CoverageMapping.cpp
  CoverageMappingWriter.cpp
  CoverageMappingReader.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/ProfileData/Coverage

  DEPENDS
  intrinsics_gen
  )
