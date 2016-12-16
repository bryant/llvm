include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(PPP)
  set(LLVM_LINK_COMPONENTS MC MCParser Support HexagonDesc HexagonInfo)
endif(PPP)
add_llvm_library(LLVMHexagonAsmParser
  HexagonAsmParser.cpp
  )

add_dependencies( LLVMHexagonAsmParser HexagonCommonTableGen )
