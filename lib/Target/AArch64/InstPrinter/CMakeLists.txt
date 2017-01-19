include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

add_llvm_library(LLVMAArch64AsmPrinter
  AArch64InstPrinter.cpp

  LINK_COMPONENTS
    AArch64Utils
    MC
    Support
)

add_dependencies(LLVMAArch64AsmPrinter AArch64CommonTableGen)
