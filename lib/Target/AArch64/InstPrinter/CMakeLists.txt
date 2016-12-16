include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS AArch64Utils MC Support)
endif(PPP)
add_llvm_library(LLVMAArch64AsmPrinter
  AArch64InstPrinter.cpp
  )

add_dependencies(LLVMAArch64AsmPrinter AArch64CommonTableGen)
