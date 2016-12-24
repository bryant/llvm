include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS AArch64Desc AArch64Info AArch64Utils MC MCDisassembler Support)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMAArch64Disassembler
  AArch64Disassembler.cpp
  AArch64ExternalSymbolizer.cpp
  )

add_dependencies(LLVMAArch64Disassembler AArch64CommonTableGen)
