include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAArch64Info
  AArch64TargetInfo.cpp
  )

add_dependencies(LLVMAArch64Info AArch64CommonTableGen)
