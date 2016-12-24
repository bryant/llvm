if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Core Object ProfileData Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMCoverage
  CoverageMapping.cpp
  CoverageMappingWriter.cpp
  CoverageMappingReader.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/ProfileData/Coverage

  DEPENDS
  intrinsics_gen
  )
