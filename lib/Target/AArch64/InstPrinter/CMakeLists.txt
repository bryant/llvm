include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS AArch64Utils MC Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAArch64AsmPrinter
  AArch64InstPrinter.cpp
  )

add_dependencies(LLVMAArch64AsmPrinter AArch64CommonTableGen)
