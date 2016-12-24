include_directories( ${CMAKE_CURRENT_BINARY_DIR}/.. ${CMAKE_CURRENT_SOURCE_DIR}/.. )

if(WITHOUT_LLVMBUILD)
  set(LLVM_LINK_COMPONENTS MC MCParser Support LanaiDesc LanaiInfo)
endif(WITHOUT_LLVMBUILD)
add_llvm_library(LLVMLanaiAsmParser
  LanaiAsmParser.cpp
  )

add_dependencies( LLVMLanaiAsmParser LanaiCommonTableGen )
